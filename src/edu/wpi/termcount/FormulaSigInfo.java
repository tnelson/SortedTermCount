/*
Copyright (c) 2009-2010 Brown University and Worcester Polytechnic Institute.

This file is part of Margrave.

Margrave is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Margrave is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License
along with Margrave.  If not, see <http://www.gnu.org/licenses/>.
*/ 

// Constructor takes a Kodkod Formula object and a specification
// of the sort hierarchy. See below for expectations about
// the input.

// Some optimization has been done: see SigFunction.noCondition,
// AbstractCacheAllCollector, etc.

package edu.wpi.termcount;

import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.*;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.*;
import java.math.BigInteger;

// Thrown by FormulaSigInfo if a given Formula contains 
// unsupported features or quantification over a non-sort.
class UnsupportedFormulaException extends Exception
{
	UnsupportedFormulaException(String str)
	{
		super(str);
	}
}

// Thrown if the user asks about an Expression which is not
// a sort w/r/t the given Sig.
class NotASortException extends Exception
{
	NotASortException(String str)
	{
		super(str);
	}
}

// -------- Helper class: SigFunction ----------
// Represents a function: EITHER a Skolem function or an original function.
	
class SigFunction
{
	String name;		
	List<LeafExpression> arity = new ArrayList<LeafExpression>();
	LeafExpression sort;

	
	// Does this function in fact have no conditions?
	// e.g. "\exists x^A ." 
	// Used to optimize counting: If another function of the
	// same arity and sort exists, no need to consider this one.
	boolean noCondition = false;
	
	
	
	// Was this function induced by a sort symbol appearing as a
	// predicate? (e.g., \forall x^A B(x) where A and B are sorts,
	// is interpreted by this visitor as \forall x^A \exists y^B (x=y).)
	boolean fromSortAsPredicate = false; 	
	// For SAP B(x), this will be the variable x.
	Variable tempCause = null;
	// if x is eventually existentially quantified, will be the function 
	// induced by that quantifier.
	SigFunction funcCause = null;
	
	public String getID()
	{
		// ID is the descriptor plus the object's hashcode.			
		return name + "_" +hashCode();
	}
	
	public String toString()
	{
		if(arity.size() < 1)
			return getID() + ": " + sort;
		return getID() + arity  + ": "+ sort; 
	}
	
	public String toPrettyString()
	{		
		String result;		
		if(arity.size() < 1)
			result = name + ": " + sort;
		else
			result = name + arity + ": "+ sort;
		
		if(fromSortAsPredicate)
		{
			if(funcCause == null)
				result += " [s.a.p. GLOBAL]";
			else
				result += " [s.a.p. LOCAL: " + funcCause.name + "]";
		}
		
		return result;
	}
	
	public SigFunction safeClone()
	{
		SigFunction result = new SigFunction(this.name, this.sort, this.noCondition);
		result.arity = new ArrayList<LeafExpression>(this.arity); 
		result.fromSortAsPredicate = this.fromSortAsPredicate;
		return result;
	}
	
	SigFunction(String n, LeafExpression r, boolean noCondition)
	{
		this.name = n;
		this.arity = new ArrayList<LeafExpression>();
		this.sort = r;
		this.noCondition = noCondition;
	}
	
}




public class FormulaSigInfo
{
	// -------- Helper: FuncClause -----------
	// Used in unproductive function removal
	class FuncClause
	{
		SigFunction theFunction;
		Set<LeafExpression> needed;
		LeafExpression result;
		
		FuncClause(SigFunction theFunction)
		{
			this.theFunction = theFunction;
			needed = new HashSet<LeafExpression>(theFunction.arity);
			result = theFunction.sort;
		}
		
		FuncClause(LeafExpression arity, LeafExpression sort)
		{
			// Used for inclusion functions
			this.theFunction = null;
			needed = new HashSet<LeafExpression>();
			needed.add(arity);
			result = sort;			
		}
	}
	
		
	// -------- Helper class: WalkAST ----------
	// Visitor pattern: Walks the Formula's AST
	// finding Skolem functions. Caches as much as possible. 
	
	class WalkAST extends AbstractCollector<SigFunction>
	{
		// Don't keep track of scope, so that we can cache functions.

		// A unique function object is a unique function. Make sure to clone and avoid
		// potential duplicates when the formula branches.
		
		// Note that we don't need to collect quantifiers under negations, 
		// because the formula is assumed to be in NNF.
		
		String error_condition;
		boolean error;
						
		public Set<SigFunction> newSet()
		{
			return new HashSet<SigFunction>();
		}
		
		public WalkAST()
		{		
			super(new HashSet<Node>());
			error_condition = "";
			error = false;
		}
			
		public Set<SigFunction> visit(NotFormula nf)	
		{			
			if(cache.containsKey(nf))
				return lookup(nf);
			
			cached.add(nf); // will cache a result below
			
			Set<SigFunction>  t;
			
			// Negative instance of a multiplicity?
			if(nf.formula() instanceof MultiplicityFormula)
			{
				// Negative multiplicities
				MultiplicityFormula within = (MultiplicityFormula)nf.formula();
				switch(within.multiplicity())
				{			
				case LONE:
					// 2+ -- needs 2 existentials
					t = handleMultiplicity("!lone1"+within.expression(), within.expression(), false);
					t.addAll(handleMultiplicity("!lone2"+within.expression(), within.expression(), false));
					return cache(nf, t);				
				case ONE:
					// none or 2+ -- needs 2 existentials
					t = handleMultiplicity("!one1"+within.expression(), within.expression(), false);
					t.addAll(handleMultiplicity("!one2"+within.expression(), within.expression(), false));
					return cache(nf, t);							
				case SOME:
					// negative .some is the same as positive .no, and is doable with universals only
					return cache(nf, new HashSet<SigFunction>());
				case NO:
					// same as positive .some; needs one existential.
					return cache(nf, handleMultiplicity("!no"+within.expression(), within.expression(),  true));
				}
				 
			}
			
			// Don't descend, even seeking sorts-as-predicates: negation will cause 
			// the existential they induce to become a safe forall.
			return cache(nf, new HashSet<SigFunction>());
		}
				
		public Set<SigFunction> visit(ComparisonFormula comp)
		{			
			if(cache.containsKey(comp))
				return lookup(comp);
			
			cached.add(comp);
			
			if(ExprCompOperator.SUBSET.equals(comp.op()))
			{
				// TODO more than just x in R (R1 in R2, x = R, etc.)
				
				// Treat sorts-as-predicates depending on params	
				if(! (comp.right() instanceof LeafExpression))
				{
					error = true;
					error_condition += "  Unsupported ComparisonFormula: "+comp;				
					return cache(comp, new HashSet<SigFunction>()); // fail
				}
				
				LeafExpression rel = (LeafExpression) comp.right();
				
				// Check for var in non-sort predicate (no effect)
				if(predicates.containsKey(rel))
					return cache(comp, new HashSet<SigFunction>());
				
				// sort as predicate
				if(comp.left() instanceof Variable)					
				{					
					if(sap.equals(FormulaSigInfo.EnumSAPHandling.sapIgnore))
						return cache(comp, new HashSet<SigFunction>());
					
					// The caller will decide what to do
					SigFunction newfunc = new SigFunction("SAP_VR_"+comp.toString(), rel, false);
					newfunc.fromSortAsPredicate = true;
					newfunc.tempCause = (Variable) comp.left(); // store the variable involved
					
					Set<SigFunction> result = new HashSet<SigFunction>();
					result.add(newfunc);  
					return cache(comp, result);
				}													
				
				// Otherwise it's an unsupported comparison formula
				error = true;
				error_condition += "  Unsupported ComparisonFormula: "+comp;				
				return cache(comp, new HashSet<SigFunction>()); // fail
			}
			
			// otherwise it is an equality comparison, which can't hide any Skolem functions.
			return cache(comp, new HashSet<SigFunction>());
		}
		
		public Set<SigFunction> visit(MultiplicityFormula mf)
		{
			// Positive multiplicities
			
			if(cache.containsKey(mf))
				return lookup(mf);
			
			cached.add(mf); // will cache a result below

			
			switch(mf.multiplicity())
			{
			case LONE:
				// positive .lone() is doable with universals only.
				return cache(mf, new HashSet<SigFunction>());
			case ONE:
				// one existental
				// TFC: "Total function constraint" -- want to support this...
				return cache(mf, handleMultiplicity("one"+mf.expression(), mf.expression(), true));
			case SOME:
				// one existential
				return cache(mf, handleMultiplicity("some"+mf.expression(), mf.expression(),  true));
			case NO:
				// positive .no() is doable with universals only.
				return cache(mf, new HashSet<SigFunction>());
			}
				 
			return cache(mf, new HashSet<SigFunction>());		
		}
		
		
		HashSet<SigFunction> handleMultiplicity(String name, Expression rex, boolean isSing) 
		{
			if(! (rex instanceof LeafExpression))
			{
				error = true;
				error_condition += " handleMultiplicity called with non-LeafExpression: "+rex;
				return new HashSet<SigFunction>();
			}
			LeafExpression r = (LeafExpression)rex;
						
			HashSet<SigFunction> result = new HashSet<SigFunction>();
		
			if(predicates.containsKey(r))
			{
				// Predicate may be bigger than unary.
				for(LeafExpression asort : predicates.get(r))
				{
					SigFunction f = new SigFunction(name, asort, isSing);
					result.add(f);
				}
					
			}
						
			else if(sorts.contains(r))
			{
				// copy constructor: make sure to use a different list object than what's passed.
				SigFunction f = new SigFunction(name, r, isSing);
				result.add(f);				
			}
			else
			{
				error = true;
				error_condition += " Multiplicity over non pred, non sort: "+r;
				return result;
			}
			
			return result;
		}
		
		public Set<SigFunction> visit(QuantifiedFormula q)
		{
			if(cache.containsKey(q))
				return lookup(q);
			cached.add(q);
			
			Formula within = q.formula();
			
			// Deal with the quantifier.
			if(q.quantifier().equals(Quantifier.ALL))
			{
				
				// Universal: 
				// See what functions are induced under this universal, and then add this to their params.

				// Walk the AST.
				Set<SigFunction> temp = within.accept(this);

				for(Decl d : q.decls())
				{
					// If not a LeafExpression, not supported.
					if(! (d.expression() instanceof LeafExpression))
					{
						error = true;
						error_condition += " Decl "+d+" was not over a LeafExpression";
						return new HashSet<SigFunction>();
					}
					
					if(! (Multiplicity.ONE.equals(d.multiplicity())))
					{
						error = true;
						error_condition += " Decl "+d+" did not use the ONE multiplicity. Only singleton variables are supported.";
						return new HashSet<SigFunction>();						
					}
					
					for(SigFunction f : temp)
					{
						if(!f.fromSortAsPredicate)
							f.arity.add((LeafExpression) d.expression());
						else
						{
							// Special handling for SAP functions. 
							// GLOBAL coercions: Only collect the first universal.
							// LOCAL: treat as normal
							if(f.arity.size() == 0) // always collect first universal
								f.arity.add((LeafExpression) d.expression());
							else if(f.funcCause != null) // local
								f.arity.add((LeafExpression) d.expression());
						}
					}
						
				}
				
							
				return cache(q, temp);
			}
			else
			{
				// Existential:
						
				Set<SigFunction> innerfuncs = within.accept(this);
				
				HashSet<SigFunction> thesefuncs = new HashSet<SigFunction>();
				for(Decl d : q.decls())
				{
					// If not a LeafExpression, not supported.
					if(! (d.expression() instanceof LeafExpression))
					{
						error = true;
						error_condition += " Decl "+d+" was not over a LeafExpression";
						return new HashSet<SigFunction>();
					}
					
					if(!Expression.UNIV.equals(d.expression()) && ! (d.expression() instanceof Relation))
					{
						error = true;
						error_condition += " Decl "+d+" was over a LeafExpression that was not a Relation or UNIV.";
						return new HashSet<SigFunction>();
					}					
					
					if(! (Multiplicity.ONE.equals(d.multiplicity())))
					{
						error = true;
						error_condition += " Decl "+d+" did not use the ONE multiplicity. Only singleton variables are supported.";
						return new HashSet<SigFunction>();						
					}
					
					// New induced Skolem function! (At this point, it's a constant; arity added later.)
					SigFunction f = new SigFunction(d.variable().toString(), 
							(LeafExpression)d.expression(), false);
					thesefuncs.add(f);
					
					// SAP handling: Is this quantified variable the "cause" of a SAP function?
					// e.g., the x in B(x)
					for(SigFunction sap : innerfuncs )
					{
						if(!sap.fromSortAsPredicate)
							continue;
						
						if(d.variable().equals(sap.tempCause))
							sap.funcCause = f;
					}
					
					
				}
				
				// (Don't trust returned set to be writable.)
				Set<SigFunction> result = new HashSet<SigFunction>();
				result.addAll(innerfuncs);
				result.addAll(thesefuncs);
				return cache(q, result);
			}				
		}
		
		public Set<SigFunction> visit(NaryFormula naryf)
		{
			// See visit(BinaryFormula) below for reasoning
			if(cache.containsKey(naryf))
				return lookup(naryf);
			cached.add(naryf);
			
			Set<SigFunction> result = new HashSet<SigFunction>();
			Set<SigFunction> intersection = new HashSet<SigFunction>();
			
			// Add each sub-formula's FuncStructs, but check for duplication.
			// If there are any duplicates, be sure to double-count!
			for(Formula child : naryf)
			{
				Set<SigFunction> newfuncs = child.accept(this);
				
				// Rolling check for duplicates
				intersection.clear();
				intersection.addAll(result);
				intersection.retainAll(newfuncs);
				if(newfuncs.size() > 0 && intersection.size() > 0)
				{																	
					for(SigFunction dopple : intersection)
						if(!dopple.fromSortAsPredicate) // SAP is the identity
							result.add(dopple.safeClone());
				}
				
				result.addAll(newfuncs);
				
			}
			
			
			return result;
		}
		
		
		public Set<SigFunction> visit(BinaryFormula bf)
		{
			// There are multiple branches here. Kodkod will do its best to
			// duplicate formula references, and we're using a cache in
			// this visitor. That means that we could end up having
			// the left and right branch pointing to the "same"
			// existential QuantifiedFormula object, but we need them 
			// induce separate functions. Hence the "safe cloning" below. 
								
			if(cache.containsKey(bf))
				return lookup(bf);
			cached.add(bf);

			Set<SigFunction> lfs = bf.left().accept(this);
			Set<SigFunction> rfs = bf.right().accept(this);
			
			Set<SigFunction> result = new HashSet<SigFunction>(lfs);
			result.addAll(rfs);
			
			// Do we have any references to the same FuncStruct in both sets?
			if(rfs.size() > 0 && lfs.size() > 0) // prevent exception
			{
				// (lfs, rfs may be singleton, need another mutable set to do this)
				Set<SigFunction> overlaps = new HashSet<SigFunction>(lfs);
				overlaps.retainAll(rfs);
								
				for(SigFunction dupe : overlaps)			
				{
					if(!dupe.fromSortAsPredicate) // SAP is the identity
						result.add(dupe.safeClone());
				}
			}
			
			return result;
		}		
	}

	
	
	
	
	
	
	
	
	
	
	// ------------- Sig definition ----------------
	
	// The Formula object that this object is created to analyze.
	// The formula is assumed to be in negation normal form!
	private Formula fmla;
	
	// predicate symbols (non-sort LeafExpressions)
	// Key is the predicate LeafExpression
	// Value is the vector of sorts describing the type of the predicate
	// (e.g., R \in A \times B)
	private Map<LeafExpression, List<LeafExpression>> predicates;
	
	// Set of LeafExpressions treated as sorts
	private Set<LeafExpression> sorts;
	
	// mapping from sorts to the set of all their supersorts.
	// this mapping is **assumed** to be
	// - A partial order
	// - transitively closed
	// - contain entries for each LeafExpression in this.sorts.	
	private Map<LeafExpression, Set<LeafExpression>> supersorts;
		
	// These are in the pre-Skolem signature.
	// Algorithmics will consider both these and the Skolem functions together.
	private Set<SigFunction> originalFunctions;
	private Set<SigFunction> originalConstants;
	
	
	//  ------------- Calculated fields  ----------------
	
	// Reverse of supersorts: calculated in constructor
	private Map<LeafExpression, Set<LeafExpression>> subsorts =
		new HashMap<LeafExpression, Set<LeafExpression>>();
	
	// Set of all Skolem functions within fmla
	private Set<SigFunction> skolemFunctions = 
		new HashSet<SigFunction>();
	// Set of all Skolem constants within fmla
	private Set<SigFunction> skolemConstants = 
		new HashSet<SigFunction>();
	
	// Set of all Skolem SAP functions within fmla
	private Set<SigFunction> sapFunctions = 
		new HashSet<SigFunction>();
	// Set of all Skolem SAP constants within fmla
	private Set<SigFunction> sapConstants = 
		new HashSet<SigFunction>();
	
	
	
	// Set of all the Skolem functions which can be used to build
	// terms over the Skolem signature (not SAP, though)
	private Set<SigFunction> productiveFunctions = 
		new HashSet<SigFunction>();
	private Set<SigFunction> productiveSAPFunctions = 
		new HashSet<SigFunction>();
	
	
	// Set of sorts which contain finitely many terms 
	private Set<LeafExpression> finitarySorts = new HashSet<LeafExpression>();
	
	// mapping from finitary sorts to the number of terms in them 
	private Map<LeafExpression, BigInteger> termCounts =
		new HashMap<LeafExpression, BigInteger>();
	
	private BigInteger totalTerms = BigInteger.ZERO;
	
	// ------------- Constructor and helpers ----------------
		
	//ThreadMXBean mxBean = ManagementFactory.getThreadMXBean();
	long msCollect = 0;
	long msProductive = 0;
	long msFinitary = 0;
	long msBounds = 0;

	//QuotaService qs = QuotaServiceFactory.getQuotaService();
    
	/**
	 * sapThrowException: Throws an exception if SAP is encountered.
	 * sapIgnore: Ignores SAP functions entirely, discarding them before counting. 
	 */
	public enum EnumSAPHandling
	{
	   sapKeep, sapThrowException, sapIgnore 
	}
	
	EnumSAPHandling sap;
	boolean htmlOutput; 
	
	// ASSUMPTIONS:
	// (1) fmla is in NNF
	// (2) supersorts is a poset (no cycles, transitive, etc.)
	FormulaSigInfo(Set<LeafExpression> sorts, 
			Map<LeafExpression, Set<LeafExpression>> supersorts,
			Map<LeafExpression, List<LeafExpression>> predicates, 
			Set<SigFunction> originalFunctions,
			Set<SigFunction> originalConstants,
			Formula fmla,
			EnumSAPHandling sap,
			boolean htmlOutput)
				throws UnsupportedFormulaException, NotASortException
	{
		init(sorts, supersorts, predicates, originalFunctions, originalConstants, fmla, sap, htmlOutput);
	}
	
	FormulaSigInfo(Set<LeafExpression> sorts, 
			Map<LeafExpression, Set<LeafExpression>> supersorts,
			Map<LeafExpression, List<LeafExpression>> predicates, 
			Set<SigFunction> originalFunctions,
			Set<SigFunction> originalConstants,
			Formula fmla,
			EnumSAPHandling sap)
	throws UnsupportedFormulaException, NotASortException
	{
		init(sorts, supersorts, predicates, originalFunctions, originalConstants, fmla, sap, false);
	}
	
	private void handleUNIV()
	{	
		// Maximal sort is maximal
		sorts.add((LeafExpression)Expression.UNIV);
		
		for(LeafExpression s : supersorts.keySet())
			supersorts.get(s).add((LeafExpression)Expression.UNIV);
		
	}
	
	private void confirmNoFunctionOrConstantOverloading()
	throws UnsupportedFormulaException
	{
		// Do not allow overloading! 
		Set<String> usedNames = new HashSet<String>();
		
		for(SigFunction f : originalFunctions)
		{
			if(usedNames.contains(f.name))
				throw new UnsupportedFormulaException("Error: The symbol "+f.name+" was declared more than once!");
			usedNames.add(f.name);
		}
		
		for(SigFunction f : originalConstants)
		{
			if(usedNames.contains(f.name))
				throw new UnsupportedFormulaException("Error: The symbol "+f.name+" was declared more than once!");
			usedNames.add(f.name);
		}
		
	}
	
	private void init(Set<LeafExpression> sorts, 
			Map<LeafExpression, Set<LeafExpression>> supersorts,
			Map<LeafExpression, List<LeafExpression>> predicates, 
			Set<SigFunction> originalFunctions,
			Set<SigFunction> originalConstants,
			Formula fmla,
			EnumSAPHandling sap,
			boolean htmlOutput)
	throws UnsupportedFormulaException, NotASortException
	{
		// Fix a set of Sorts, a partial order on them, and a Formula.
		this.fmla = fmla;
		this.supersorts = supersorts;
		this.sorts = sorts;
		this.predicates = predicates;
		
		this.sap = sap;
		this.htmlOutput = htmlOutput;
		
		// pre-Skolem functions
		this.originalConstants = originalConstants;
		this.originalFunctions = originalFunctions;
		
		confirmNoFunctionOrConstantOverloading();
		
		// Add Expression.UNIV as the ultimate supersort.
		handleUNIV();
		
		// If the caller passed a reflexive LeafExpression in supersorts, remove the self-reference.
		for(LeafExpression r : supersorts.keySet())		
			supersorts.get(r).remove(r);				
		
		// Populate subsorts map 
		// (This is used repeatedly by DFS in findProductiveFunctions; calculate ONCE.)
		for(LeafExpression parent : sorts)
		{
			subsorts.put(parent, new HashSet<LeafExpression>());
			
			// correct potential lack in supersorts
			if(!supersorts.containsKey(parent))
				supersorts.put(parent, new HashSet<LeafExpression>());
			
			// Subsorts for this parent
			for(LeafExpression sub : supersorts.keySet())
				if(supersorts.get(sub).contains(parent))
					subsorts.get(parent).add(sub);
		}		
		
		//long startMegacycles;
		long startTime;
		
		// Parse fmla looking for Skolem functions.				
//		startTime = mxBean.getCurrentThreadCpuTime();
		//startMegacycles = qs.getCpuTimeInMegaCycles();
		collectSkolemFunctions();
		//msCollect = (mxBean.getCurrentThreadCpuTime() - startTime) / 1000000;
		//mCycCollect = (qs.getCpuTimeInMegaCycles() - startMegacycles);
		
		// Make sure the formula and functions given are well-formed w/r/t the sorts given
		for(SigFunction f : skolemFunctions)
			validateFunction(f, "in the formula");
		for(SigFunction c : skolemConstants)
			validateFunction(c, "in the formula");
		for(SigFunction f : originalFunctions)
			validateFunction(f, "in the original signature");
		for(SigFunction c : originalConstants)
			validateFunction(c, "in the original signature");		
		
		// Discover and cache the set of functions which are productive.
	//	startTime = mxBean.getCurrentThreadCpuTime();
		//startMegacycles = qs.getCpuTimeInMegaCycles();
		findProductiveFunctions();
	//	msProductive = (mxBean.getCurrentThreadCpuTime() - startTime) / 1000000;
		//mCycProductive = (qs.getCpuTimeInMegaCycles() - startMegacycles);
		
		// Do a cycle check to find finitary sorts
		//startTime = mxBean.getCurrentThreadCpuTime();
		//startMegacycles = qs.getCpuTimeInMegaCycles();
		findFinitarySorts();
	//	msFinitary = (mxBean.getCurrentThreadCpuTime() - startTime) / 1000000;
		//mCycFinitary = (qs.getCpuTimeInMegaCycles() - startMegacycles);
		
		// Finally, calculate bounds for finitary sorts
	//	startTime = mxBean.getCurrentThreadCpuTime();
		//startMegacycles = qs.getCpuTimeInMegaCycles();
		calculateBounds();
	//	msBounds = (mxBean.getCurrentThreadCpuTime() - startTime) / 1000000;	
		//mCycBounds = (qs.getCpuTimeInMegaCycles() - startMegacycles);
	}
	
	
	private void validateFunction(SigFunction f, String appearedAs)
	throws NotASortException
	{
		for(LeafExpression inArity : f.arity)
			if(!sorts.contains(inArity))
				throw new NotASortException("The LeafExpression "+inArity.toString() + 
						" appeared as a sort symbol "+appearedAs+", but was not declared to be a sort.");
		
		if(!sorts.contains(f.sort))
			throw new NotASortException("The LeafExpression "+f.sort.toString() + 
				" appeared as a sort symbol "+appearedAs+", but was not declared to be a sort.");		
	}
	
	private void collectSkolemFunctions()
	throws UnsupportedFormulaException
	{
		WalkAST walker = new WalkAST();
		Set<SigFunction> results = fmla.accept(walker);
		if(walker.error)
		{
			System.err.println(walker.error_condition);
			throw new UnsupportedFormulaException(walker.error_condition);
		}
		
		// **************************
		// Which of these were SAP?
		// **************************
		
		for(SigFunction f : results)
			if(f.fromSortAsPredicate)
			{
				if(f.arity.size() == 0)
					sapConstants.add(f);
				else
					sapFunctions.add(f);
			}
			
		results.removeAll(sapConstants);
		results.removeAll(sapFunctions);
		
		if(sap.equals(EnumSAPHandling.sapThrowException))
		{
			// sapThrowException
			throw new UnsupportedFormulaException("Sort symbol was used as predicate and handler was set to disallow this.");
		}
		else if(sap.equals(EnumSAPHandling.sapIgnore))
		{
			sapConstants.clear();
			sapFunctions.clear();
		}
		// Otherwise, keep and deal with in term counting
				
		skolemFunctions.clear();
		skolemConstants.clear();
		for(SigFunction f : results)
		{
			if(f.arity.size() == 0)
				skolemConstants.add(f);
			else
				skolemFunctions.add(f);
		}
		
		// Optimization:
		// Remove "no condition" constants covered by others.
		// (e.g., suppose "exists x^A and some A" -- don't need
		// to include the "some A" constant.)
		Set<SigFunction> toRemove = new HashSet<SigFunction>();
		for(SigFunction c : skolemConstants)
		{
			if(c.noCondition)
			{
				// All constants (not just Skolem)
				Set<SigFunction> allConstants = new HashSet<SigFunction>(originalConstants);
				allConstants.addAll(skolemConstants);
				
				for(SigFunction otherc : allConstants)
				{
					// Found a different constant of same (or super-) sort
					// which is not currently flagged for removal by this loop
					if(c != otherc && otherc.arity.size() == 0 && !toRemove.contains(otherc) &&
							(c.sort == otherc.sort || supersorts.get(otherc.sort).contains(c.sort)))
					{
						toRemove.add(c);
						break; // next outer loop iteration
					}
				}
				
			}			
		}
		skolemConstants.removeAll(toRemove); // don't keep superfluous "some" constants
	}
	
	private void findProductiveFunctions()
	{	
		productiveFunctions.clear();

		// Start with an ordering on all the functions, represented as clauses
		Set<FuncClause> funcList = new HashSet<FuncClause>();
		for(SigFunction f : skolemFunctions)
			funcList.add(new FuncClause(f));	
		for(SigFunction f : originalFunctions)
			funcList.add(new FuncClause(f));	
		for(SigFunction f : sapFunctions)
			funcList.add(new FuncClause(f));	
		
				
		// For simplicity in this algorithm, treat the sort ordering as a set of inclusion functions.		
		for(LeafExpression sub : supersorts.keySet())
			for(LeafExpression sup : supersorts.get(sub))
				funcList.add(new FuncClause(sub, sup));
		
		// and an ordering on the sorts of constant symbols (to start)
		Queue<LeafExpression> units = new LinkedList<LeafExpression>();
		for(SigFunction c : skolemConstants)
			if(!units.contains(c.sort))
				units.add(c.sort);
		for(SigFunction c : originalConstants)
			if(!units.contains(c.sort))
				units.add(c.sort);
		for(SigFunction c : sapConstants)
			if(!units.contains(c.sort))
				units.add(c.sort);
		
		// for each sort, keep a list of clauses in whose arity it appears
		Map<LeafExpression, Set<FuncClause>> sortsToFuncs = new HashMap<LeafExpression, Set<FuncClause>>();
		for(FuncClause fc : funcList)
		{
			for(LeafExpression anAritySort : fc.needed)
			{
				if(!sortsToFuncs.containsKey(anAritySort))
					sortsToFuncs.put(anAritySort, new HashSet<FuncClause>());
				sortsToFuncs.get(anAritySort).add(fc);				
			}					
		}
		
		// propagate units until done
		Set<LeafExpression> alreadyPropagated = new HashSet<LeafExpression>();
		while(units.size() > 0)			
		{
			LeafExpression rel = units.remove();
			if(alreadyPropagated.contains(rel))
				continue;			
			alreadyPropagated.add(rel);
			
			// TODO: This LeafExpression (rel) is _populated_ (not term-free). useful info.
			
			// what func clauses require rel to fire?
			if(sortsToFuncs.containsKey(rel))
			{				
				for(FuncClause fc : sortsToFuncs.get(rel))
				{
					fc.needed.remove(rel); // this part of f's arity is populated
					
					if(fc.needed.size() == 0) // f's arities are all populated; f can fire 
					{
						if(fc.theFunction != null) // not an inclusion
							productiveFunctions.add(fc.theFunction);						
						units.add(fc.result);
					}
				}
			}
		}
		
		// Split productiveFunctions and productiveSAPFunctions.
		productiveSAPFunctions.clear();
		for(SigFunction f : productiveFunctions)
			if(f.fromSortAsPredicate)
				productiveSAPFunctions.add(f);
		
		productiveFunctions.removeAll(productiveSAPFunctions);
					
	}
	
	private void findFinitarySorts()
	{
		// Precondition: unproductive functions removed.
		
		// DFS amongst sorts via these arcs: 
		// (1) supersort LeafExpression 
		// (2) inverted shadow-edges in dependency graph of _productive_ functions 
		// (3) inverted shadow-edges in dependency graph of productive SAP functions
		// (4) SAP coercions
		// seek cycles. on stack when cycle with a non-SAP function found = infinitary.
				
		final Set<LeafExpression> todo = new HashSet<LeafExpression>(sorts);
		final Set<LeafExpression> finitary = new HashSet<LeafExpression>();
		final HashMap<LeafExpression, Set<LeafExpression>> arcs = new HashMap<LeafExpression, Set<LeafExpression>>();
		final HashMap<LeafExpression, Set<LeafExpression>> canUseRealFunction = new HashMap<LeafExpression, Set<LeafExpression>>();
		
		final HashMap<LeafExpression, Set<LeafExpression>> takenArcs = new HashMap<LeafExpression, Set<LeafExpression>>();

		// init
		for(LeafExpression curr : todo)
		{
			arcs.put(curr, new HashSet<LeafExpression>());
			canUseRealFunction.put(curr, new HashSet<LeafExpression>());
			takenArcs.put(curr, new HashSet<LeafExpression>());
		}

		// real functions flowing in
		for(SigFunction f : productiveFunctions)				
			for(LeafExpression arg : f.arity)
			{
				arcs.get(f.sort).add(arg);	
				canUseRealFunction.get(f.sort).add(arg);
			}
		
		// Subsorts
		for(LeafExpression curr : todo)
			arcs.get(curr).addAll(subsorts.get(curr));
				
		// coercions due to SAP functions (global and local)
		for(SigFunction f : productiveSAPFunctions)	
			for(LeafExpression arg : f.arity)
				arcs.get(f.sort).add(arg);
		
		
		while(todo.size() > 0)
		{			
			// Get an arbitrary element of unknown:
			LeafExpression curr = todo.iterator().next();
			Stack<LeafExpression> thispath = new Stack<LeafExpression>();
			
			doSortDFS(arcs, takenArcs, canUseRealFunction, curr, todo, finitary, thispath);
			//System.out.println("DFS complete. Unknown remaining: "+todo);
		}			
		
		finitarySorts.clear();
		finitarySorts.addAll(finitary);		
	}
	
	private boolean doSortDFS(
			HashMap<LeafExpression, Set<LeafExpression>> arcs, 
			HashMap<LeafExpression, Set<LeafExpression>> takenArcs,
			HashMap<LeafExpression, Set<LeafExpression>> canUseRealFunction, 
			
			LeafExpression curr, Set<LeafExpression> todo, Set<LeafExpression> finitary, Stack<LeafExpression> thispath)
	{
		// Options to search through: all arcs not yet taken
		// Always prioritize exploration (visiting sorts not on stack) or we lose correctness
		
		Set<LeafExpression> optionsExplore = new HashSet<LeafExpression>(arcs.get(curr));
		optionsExplore.removeAll(takenArcs.get(curr));
		Set<LeafExpression> optionsDefer = new HashSet<LeafExpression>();
		for(LeafExpression opt : optionsExplore)
		{
			if(thispath.contains(opt))
				optionsDefer.add(opt);
		}
		optionsExplore.removeAll(optionsDefer);
		
		
		//System.out.println("curr = "+curr);
		//System.out.println("optionsExplore = "+optionsExplore);
		//System.out.println("optionsDefer = "+optionsDefer);
		//System.out.println("thispath = "+thispath);
		//System.out.println();
		
		List<LeafExpression> optionsInOrder = new ArrayList<LeafExpression>(optionsExplore.size() + optionsDefer.size());
		optionsInOrder.addAll(optionsExplore);
		optionsInOrder.addAll(optionsDefer);
		
		for(LeafExpression next : optionsInOrder)
		{
			// check off this arc
			takenArcs.get(curr).add(next);
			
			if(!todo.contains(next))
			{
				// next is known to be infinitary
				if(!finitary.contains(next))
				{
					//System.err.println(curr + " was marked infinitary since "+next+" was.");
					todo.remove(curr);
					return false; 
				}
				// next has been fully checked and shown to be finitary. no new info that way.
				else
					continue; 
			}

			boolean taintedCycle = false;
			
			if(thispath.contains(next))
			{
				//System.out.println("Detected thispath contained next: "+next+" thispath: "+thispath);
				
				// TODO efficiency: don't need to check ENTIRE stack, right? Could also carry an array of booleans?
				
				// Is the cycle tainted?
				int idx = thispath.lastIndexOf(next);
				int maxIdx = thispath.size() - 1;
				for(int iCount = idx;iCount<=maxIdx;iCount++)
				{
					LeafExpression toRel = curr;
					if(iCount < maxIdx)
						toRel = thispath.get(iCount + 1);
					
					// Could this arc use a func?
					if(canUseRealFunction.get(thispath.get(iCount)).contains(toRel))
					{
						taintedCycle = true;
						break;
					}
					
				} // end for each part of potential cycle
				
				// is the next hop going to be the real function?
				if(canUseRealFunction.get(curr).contains(next))
					taintedCycle = true;
			}
			else if(next == curr)
			{
				// cycle of length 1 -- curr isnt on the stack yet!
				if(canUseRealFunction.get(curr).contains(curr))
					taintedCycle = true;
			}
						
			// if we used a real function, found a "tainted cycle". 
			// (if not, go ahead and follow)
			if(taintedCycle)
			{		
				//System.err.println("Cycle w/ real function! "+thispath + " top: "+thispath.peek());
				
				todo.remove(curr);
				return false;
			}
			else
			{

				//System.out.println("recursing from "+curr+" to "+next);				
				
				thispath.push(curr); // leave a trail of breadcrumbs
				boolean safe = doSortDFS(arcs, takenArcs, canUseRealFunction, next, todo, finitary, thispath);
				thispath.pop(); // eat the breadcrumbs on the way back
				
				//System.out.println("safe: "+safe+", next="+next);
				
				// Found an infinitary sort that flows into curr. curr is infinitary, too.
				if(!safe)
				{
					todo.remove(curr);
					return false;
				}
			}
		}
				
		// Only reach this point if all reachable sorts have been shown finitary.
		// (This is because we explore before deferring, above)
		
		//System.out.println("safe: "+curr+"; options were: "+optionsExplore +" and "+optionsDefer +" in order: "+optionsInOrder+", stack was: "+thispath);
		finitary.add(curr);
		todo.remove(curr);
		return true;
	}
	
	private void calculateBounds()
	{
		// If all sorts are infinitary...
		if(finitarySorts.size() < 1)
			return;
		
		// ---------------------------------------------------------------
		// Create table for DP. Rows = term heights. Cols = finitary sorts.
		BigInteger[][] totals = new BigInteger[productiveFunctions.size() + 1][finitarySorts.size()];	
		
		// Initialize
		for(int iRow = 0; iRow <= productiveFunctions.size();iRow++)
			for(int iCol=0;iCol < finitarySorts.size();iCol++)
				totals[iRow][iCol] = BigInteger.ZERO;
		
		
		// Fix an ordering of the finitary sorts
		Map<LeafExpression, Integer> sortsInOrder = new HashMap<LeafExpression, Integer>();
		int ii = 0;
		for(LeafExpression s : finitarySorts)
		{
			sortsInOrder.put(s, Integer.valueOf(ii));
			ii++;
		}
		
		// And an ordering of the non-constant functions
		Map<SigFunction, Integer> funcsInOrder = new HashMap<SigFunction, Integer>();
		ii = 0;
		for(SigFunction f : productiveFunctions)
		{
			funcsInOrder.put(f, Integer.valueOf(ii));
			ii++;
		}
		
		// ---------------------------------------------------------------
		// Step 1: Populate the height=0 row with constant terms
		Set<SigFunction> allConstants = new HashSet<SigFunction>(originalConstants);
		allConstants.addAll(skolemConstants);
		
		for(SigFunction c : allConstants)
		{			
			// First, build a list of all native sorts for c. 
			// (c.sort, but also coercions due to sort-as-predicate appearance)			
			Set<LeafExpression> toPopulate = new HashSet<LeafExpression>();
			// native w/o coercion
			if(finitarySorts.contains(c.sort))
				toPopulate.add(c.sort);
			// SAP coercions (from SAP constants)
			for(SigFunction sc : sapConstants)
				if(sc.funcCause.equals(c) && finitarySorts.contains(sc.sort))
					toPopulate.add(sc.sort);
			// SAP coercions (from SAP functions)
			for(SigFunction sf : sapFunctions)
				if(sf.funcCause == null) // coercion not specific to a skolem function
					if(sf.arity.get(0).equals(c.sort) && finitarySorts.contains(sf.sort))
						toPopulate.add(sf.sort);

			// only one actual ELEMENT bound to this constant
			totalTerms = totalTerms.add(BigInteger.ONE);
			
			Set<LeafExpression> countedIn = new HashSet<LeafExpression>();
			
			for(LeafExpression pop : toPopulate)
			{
				// don't duplicate
				if(countedIn.contains(pop))
					continue;
				
				// Populate
				totals[0][sortsInOrder.get(pop).intValue()] =
					totals[0][sortsInOrder.get(pop).intValue()].add(BigInteger.ONE);
				//System.out.println("Populated: "+pop);

				
				// Propagate (<=) -- don't duplicate!
				for(LeafExpression r : supersorts.get(pop))
				{
					if(r == pop) continue;
					if(!finitarySorts.contains(r)) continue; // don't prop to inf sort
					if(countedIn.contains(r)) // don't duplicate
						continue;
					totals[0][sortsInOrder.get(r).intValue()] = 
						totals[0][sortsInOrder.get(r).intValue()].add(BigInteger.ONE);
					
					//System.out.println("Propagated: "+pop);
					countedIn.add(r); 
				} // end for each sort to propagate

				countedIn.add(pop); 
			} // end for each native sort to populate
										
		} // end for each constant

		
		
		
		// ---------------------------------------------------------------
		// Step 2: Populate each height > 0
		
		for(int height = 1; height<= productiveFunctions.size(); height++)
		{			
			// No point in going to the next height if this height has no terms.
			boolean thisHeightExists = false;
			
			for(SigFunction f : productiveFunctions)
			{
				// First, build a list of all native sorts for f's result. 
				// (f.sort, but also local coercions due to sort-as-predicate appearance)			
				Set<LeafExpression> toPopulate = new HashSet<LeafExpression>();
				// native w/o coercion
				if(finitarySorts.contains(f.sort))
					toPopulate.add(f.sort);
				// SAP coercions (from SAP functions local to f)
				for(SigFunction sc : sapFunctions)
					if(f.equals(sc.funcCause) && finitarySorts.contains(sc.sort))
						toPopulate.add(sc.sort);
				// SAP coercions (from SAP functions which are global coercions)
				for(SigFunction sf : sapFunctions)
					if(sf.funcCause == null) // coercion not specific to a Skolem function
						if(sf.arity.get(0).equals(f.sort) && finitarySorts.contains(sf.sort))
							toPopulate.add(sf.sort);
				
				if(toPopulate.size() == 0)
					continue; // don't calculate if nowhere to populate.
				
				// Calculate
				BigInteger num_this_height = BigInteger.ZERO;
				
				// To make a term of height h, there must be at least one subterm of 
				// height h-1. Consider all cases for this subterm.
				for(int ileftmost = 0; ileftmost < f.arity.size(); ileftmost++)
				{
					BigInteger num_leftmost = BigInteger.ONE;
					
					for(int icol = 0; icol < f.arity.size(); icol++ )
					{
						BigInteger coltotal = BigInteger.ZERO;
						
						if(!finitarySorts.contains(f.arity.get(icol)))
						{
							System.out.println("Error: "+f+"\n"+finitarySorts);
							System.out.println(toPopulate); // 0 is in toPopulate. why? Because we have a coercion function... then why isn't 0 infinitary?
							System.out.println(sapFunctions);
							System.out.println(productiveFunctions);
							System.exit(1);
							
						}
						// icol is indexing by position in arity list. Sort ordering is different.
						int actual_col = sortsInOrder.get(f.arity.get(icol)).intValue();
											
						
						// TODO cache column totals up to h-2 in order to save totaling time	
						
						if(icol < ileftmost)
							for(int irow=0;irow<=height-2;irow++)
								coltotal = coltotal.add(totals[irow][actual_col]);
						else if(icol > ileftmost)
							for(int irow=0;irow<=height-1;irow++)
								coltotal = coltotal.add(totals[irow][actual_col]);
						else
							coltotal = totals[height-1][actual_col];
													
						num_leftmost = num_leftmost.multiply(coltotal);
					}
										
					num_this_height = num_this_height.add(num_leftmost);
				}
								
				// Only this many actual bindings
				totalTerms = totalTerms.add(num_this_height);
				
				Set<LeafExpression> countedIn = new HashSet<LeafExpression>();
				for(LeafExpression pop : toPopulate)
				{
					// don't duplicate
					if(countedIn.contains(pop))
						continue;

					// Populate
					totals[height][sortsInOrder.get(pop).intValue()] =
						totals[height][sortsInOrder.get(pop).intValue()].add(num_this_height);						
					
					// Propagate
					for(LeafExpression r : supersorts.get(pop))
					{
						// don't duplicate
						if(countedIn.contains(r))
							continue;
						
						if(r == pop) continue;
						if(!finitarySorts.contains(r)) continue; // don't prop to inf sort
						totals[height][sortsInOrder.get(r).intValue()] =
							totals[height][sortsInOrder.get(r).intValue()].add(num_this_height);
						countedIn.add(r);
					}
					
					countedIn.add(pop);
				}
				
				if(num_this_height.compareTo(BigInteger.ZERO) == 1)
					thisHeightExists = true;
			}
			
			if(!thisHeightExists)
				break; // didn't make any height=h terms. So no h+1 can exist either.
		}
		
		// ---------------------------------------------------------------
		// Step 3: Column totals are our term counts (for finitary sorts).
		for(LeafExpression s : finitarySorts)
		{
			BigInteger total = BigInteger.ZERO;
			for(ii = 0; ii <= productiveFunctions.size(); ii++)
				total = total.add(totals[ii][sortsInOrder.get(s).intValue()]);
			termCounts.put(s, total);			
		}
		
	}
	
	
	// ------------- Unit tests ----------------
	
	public static void unitTests() 
	throws UnsupportedFormulaException, NotASortException
	{
		LeafExpression Sort1 = Relation.unary("Sort1");
		LeafExpression Sort2 = Relation.unary("Sort2");;
		
		Set<LeafExpression> sorts1 = new HashSet<LeafExpression>();
		sorts1.add(Sort1); sorts1.add(Sort2);
		
		Map<LeafExpression, Set<LeafExpression>> order1 = new HashMap<LeafExpression, Set<LeafExpression>>();
		order1.put(Sort1, new HashSet<LeafExpression>());
		order1.put(Sort2, new HashSet<LeafExpression>());
		
		Map<LeafExpression, List<LeafExpression>> predicates = new HashMap<LeafExpression, List<LeafExpression>>();
		
		Variable x = Variable.unary("x");
		Variable y = Variable.unary("y");
		Variable z = Variable.unary("z");
		
		Formula fmla1 = Sort1.some();
		Formula fmla2 = Sort1.some().and(Sort2.lone());
		Formula fmla3 = Sort1.some().and(Sort2.one());
		Formula fmla4 = Sort1.some().and(Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1)));

		// two _different_ formula values
		Formula fmla5 = fmla4.and(Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1)));
		Formula fmla6 = fmla5.and(Formula.TRUE.forSome(x.oneOf(Sort1)));
		
		// SAME formula values.
		Formula subf = Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1));
		Formula fmla7 = Sort1.some().and(subf).and(subf);
		
		// Same as fmla7, but using an nary formula (3+ subfs)
		// Need to hide them (since set doesn't allow real duplicates)
		Set<Formula> theconj = new HashSet<Formula>();
		theconj.add(subf);
		theconj.add(subf.or(Formula.FALSE));
		theconj.add(subf.and(Formula.TRUE));
		Formula fmla8 = Sort1.some().and(Formula.and(theconj));
		
		// Test arity>1
		Formula fmla9 = Sort1.some()
  		  .and(Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1)).forAll(z.oneOf(Sort1)));
		
		// Test w/ more than one Decl per quantifier
		Formula fmla9a = Sort1.some()
		  .and(Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1).and(z.oneOf(Sort1))));
		
		Set<SigFunction> emptyFunctions = new HashSet<SigFunction>();
		Set<SigFunction> emptyConstants = new HashSet<SigFunction>();
		
		FormulaSigInfo test1 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla1, EnumSAPHandling.sapKeep);
		FormulaSigInfo test2 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla2, EnumSAPHandling.sapKeep);
		FormulaSigInfo test3 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla3, EnumSAPHandling.sapKeep);
		FormulaSigInfo test4 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla4, EnumSAPHandling.sapKeep);
		FormulaSigInfo test5 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla5, EnumSAPHandling.sapKeep);
		FormulaSigInfo test6 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla6, EnumSAPHandling.sapKeep);
		FormulaSigInfo test7 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla7, EnumSAPHandling.sapKeep);
		FormulaSigInfo test8 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla8, EnumSAPHandling.sapKeep);
		FormulaSigInfo test9 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla9, EnumSAPHandling.sapKeep);
		FormulaSigInfo test9a = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla9a, EnumSAPHandling.sapKeep);
		
		// 1 in Sort1
		if(test1.getTermCount() != 1)
			System.err.println("FormulaSigInfo test case 1 failed.");
		
		// 1 in Sort1 (lone doesn't induce a skolem constant)
		if(test2.getTermCount() != 1)
			System.err.println("FormulaSigInfo test case 2 failed.");

		// 1 in Sort1, 1 in Sort2 
		if(test3.getTermCount() != 2 || test3.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 3 failed.");

		// f: Sort1->Sort2, one const of sort 1
		if(test4.getTermCount() != 2 || test4.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 4 failed.");
		
		// Sort2: 2, Sort1: 1. (c1, f(c1), g(c1))
		if(test5.getTermCount() != 3 || test5.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 5 failed.");

		// f and g: 1->2 but only one constant (one was induced by a .some())
		if(test6.getTermCount() != 3 || test6.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 6 failed.");
				
		// same as test5, but identical skolem function inducing nodes
		// Sort2: 2, Sort1: 1
		if(test7.getTermCount() != 3 || test7.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 7 failed.");
		
		// now test the same phenomenon on an Nary formula.
		// Sort2: 3, Sort1=1
		if(test8.getTermCount() != 4 || test8.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 8 failed.");
		
		// Both have f(1, 1) -> 2, only one constant in sort 1.
		if(test9.getTermCount() != 2 || test9.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 9 failed.");
		if(test9a.getTermCount() != 2 || test9a.finitarySorts.size() != 3)
			System.err.println("FormulaSigInfo test case 9a failed.");

		
		
		LeafExpression Sort3 = Relation.unary("Sort3");
		Formula fmla10 = Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort1))
						.and(Formula.TRUE.forSome(x.oneOf(Sort2)).forAll(y.oneOf(Sort3)))
						.and(Sort1.some());
		sorts1.add(Sort3);
		order1.put(Sort3, new HashSet<LeafExpression>());
		FormulaSigInfo test10 = new FormulaSigInfo(sorts1, order1, predicates, emptyFunctions, emptyConstants, fmla10, EnumSAPHandling.sapKeep);
		if(test10.getTermCount() != 2 || test10.productiveFunctions.size() != 1)
			System.err.println("FormulaSigInfo test case 10 failed.");
		
		
		// A, B, C: A < B, A < C. (This is not locally filtered, but should count properly.)
		LeafExpression A = Relation.unary("A");
		LeafExpression B = Relation.unary("B");
		LeafExpression C = Relation.unary("C");
		Set<LeafExpression> sorts2 = new HashSet<LeafExpression>();
		sorts2.add(A);
		sorts2.add(B);
		sorts2.add(C);
		Map<LeafExpression, Set<LeafExpression>> order2 = new HashMap<LeafExpression, Set<LeafExpression>>();
		order2.put(A, new HashSet<LeafExpression>());
		order2.put(A, new HashSet<LeafExpression>());
		order2.get(A).add(B);
		order2.get(A).add(C);
		
		Formula fmla11 = Formula.TRUE.forSome(x.oneOf(A)).forSome(y.oneOf(B)).forSome(z.oneOf(C));
		FormulaSigInfo test11 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla11,EnumSAPHandling.sapKeep);
		if(test11.getTermCount() != 3)
			System.err.println("FormulaSigInfo test case 11 failed.");		
		
		// *************************
		// SAP Tests
		// *************************
		
		// Test simple constant->constant SAP coercion
		Formula fmla12 = x.in(C).forSome(x.oneOf(B));
		FormulaSigInfo test12 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla12, EnumSAPHandling.sapKeep);
		if(test12.getTermCount() != 1 || test12.getTermCount(B) != 1 || test12.getTermCount(C) != 1 || test12.getTermCount(A) != 0)
			System.err.println("FormulaSigInfo test case 12 failed.");		
		
		// Test simple constant + coercion function SAP
		Formula fmla13 = x.in(C).forAll(x.oneOf(B)).forSome(y.oneOf(A)).forSome(z.oneOf(B));
		FormulaSigInfo test13 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla13, EnumSAPHandling.sapKeep);		
		if(test13.getTermCount() != 2 || test13.getTermCount(B) != 2 || test13.getTermCount(C) != 2 || test13.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 13 failed.");		
		
		// Test finite number of terms via coercion function to subsort
		// (Cycle detection needs to require a normal function on the cycle)
		Formula fmla14 = x.in(A).forAll(x.oneOf(B)).forSome(y.oneOf(B));
		FormulaSigInfo test14 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla14, EnumSAPHandling.sapKeep);
		if(test14.getTermCount() != 1 || test14.getTermCount(B) != 1 || test14.getTermCount(C) != 1 || test14.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 14 failed.");							
		
		// Test infinitary (y: B, z[B]:B -- so B infinitary)
		// The result of z[b] is always in A as well as B (by SAP coercion). So inf A too.
		// Since C is a supersort of A, it must also be infinitary!
		Formula fmla15 = z.in(A).forSome(z.oneOf(B)).forAll(x.oneOf(B)).forSome(y.oneOf(B)).and(C.some());;
		FormulaSigInfo test15 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla15, EnumSAPHandling.sapKeep);		
		if(test15.getTermCount() != -1 || test15.getTermCount(B) != -1 || test15.getTermCount(C) != -1 || test15.getTermCount(A) != -1)
			System.err.println("FormulaSigInfo test case 15 failed.");		
		
		// Test partial infinitary, partial finitary
		// Changed only the coercion sort from test 15, but it prevents the infinitaryness from leaking into A (and from there, to C)
		Formula fmla16 = z.in(B).forSome(z.oneOf(B)).forAll(x.oneOf(B)).forSome(y.oneOf(B)).and(C.some());
		FormulaSigInfo test16 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla16, EnumSAPHandling.sapKeep);
		if(test16.getTermCount() != -1 || test16.getTermCount(B) != -1 || test16.getTermCount(C) != 1 || test16.getTermCount(A) != 0)
			System.err.println("FormulaSigInfo test case 16 failed.");	
		
		
		// Test coercion function in presence of real function
		
		// First, no coercion. x:A (and hence in both B and C.) f:B->C. So 2 terms in C.
		Formula fmla17 = Formula.TRUE.forSome(y.oneOf(C)).forAll(x.oneOf(B)).and(A.some());
		FormulaSigInfo test17 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla17, EnumSAPHandling.sapKeep);
		if(test17.getTermCount() != 2 || test17.getTermCount(B) != 1 || test17.getTermCount(C) != 2 || test17.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 17 failed.");
		
		// second, force C in B via SAP. Now only A is still finitary
		Formula fmla18 = Formula.TRUE.forSome(y.oneOf(C)).forAll(x.oneOf(B)).and(A.some())
		                 .and(x.in(B).forAll(x.oneOf(C)));
		FormulaSigInfo test18 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla18, EnumSAPHandling.sapKeep);
		if(test18.getTermCount() != -1 || test18.getTermCount(B) != -1 || test18.getTermCount(C) != -1 || test18.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 18 failed.");	
		

		// Term counting *propagates* for SAP coercion functions
		// z: A, f: A->B. But coerce all of B into C. f(z) must be propagated to C. (so |C| = 2)
		Formula fmla19 = Formula.TRUE.forSome(y.oneOf(B)).forAll(x.oneOf(A)).and(A.some())
        		          .and(x.in(C).forAll(x.oneOf(B)));
		FormulaSigInfo test19 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla19, EnumSAPHandling.sapKeep);
		if(test19.getTermCount() != 2 || test19.getTermCount(B) != 2 || test19.getTermCount(C) != 2 || test19.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 19 failed.");	
		//test19.printInfo();

		// Term counting *populates* for SAP "extra sort" functions
		// z:A. f: A->B. But f's output is coerced to C as well.
		Formula fmla20 = y.in(C).forSome(y.oneOf(B)).forAll(x.oneOf(A)).and(A.some());        
		FormulaSigInfo test20 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla20, EnumSAPHandling.sapKeep);
		if(test20.getTermCount() != 2 || test20.getTermCount(B) != 2 || test20.getTermCount(C) != 2 || test20.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 20 failed.");	
		
		// test local SAP coercions have same arity as the real function they come from
		Formula fmla21 = z.in(A).forSome(z.oneOf(C)).forAll(y.oneOf(B)).forAll(x.oneOf(A)).and(B.some());        
		FormulaSigInfo test21 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla21, EnumSAPHandling.sapKeep);
		if(test21.getTermCount() != 1 || test21.getTermCount(B) != 1 || test21.getTermCount(C) != 0 || test21.getTermCount(A) != 0)
			System.err.println("FormulaSigInfo test case 21 failed.");	
		
		// both funcs are useless (A is empty unless f can produce a term, but f needs something from A.)
		if(test21.productiveFunctions.size() != 0 || test21.productiveSAPFunctions.size() != 0)
			System.err.println("FormulaSigInfo test case 21(a) failed.");
	
		
		// test no doublecounting.
		// Say forall x^B, C(x) or A(x).
		Formula fmla22 = (x.in(A).or(x.in(C))).forAll(x.oneOf(B)).and(B.some());        
		FormulaSigInfo test22 = new FormulaSigInfo(sorts2, order2, predicates, emptyFunctions, emptyConstants, fmla22, EnumSAPHandling.sapKeep);
		if(test22.getTermCount() != 1 || test22.getTermCount(B) != 1 || test22.getTermCount(C) != 1 || test22.getTermCount(A) != 1)
			System.err.println("FormulaSigInfo test case 22 failed.");	
		
		
		
		
		// need more devious test cases involving case 20's kind of SAP (not a coercion -- just another result sort)
		
		
		
		
				
		// TODO what is the semantics of \forall x^A B.some ?
		// It seems as if these "noCondition" functions never go beyond arity 0?
		// (Double-check in Alloy book. If so, prevent application of \forall to them in WalkAST)
		
	}
	
	// ------------- Interface ----------------

	public int getTermCount(LeafExpression s)
	throws NotASortException
	{		
		if(!sorts.contains(s))
			throw new NotASortException("isSortFinitary: LeafExpression "+s+" was not declared as a sort.");
		if(!finitarySorts.contains(s))
			return -1;
		if(termCounts.containsKey(s))
			return termCounts.get(s).intValue();
		return -1;
	}
	
	public int getTermCount()
	{
		// It is not safe to add together all "top" sorts, because the caller 
		// may have given us an ordering that isn't locally filtered. Consider:
		// A<B, A<C with terms in A.
		
		if(finitarySorts.size() != sorts.size())
			return -1; 
		
		// Don't allow huge amounts of terms. Can change this if it is needed. 		
		if(totalTerms.bitLength() > 30)
			return -1;
		
		return totalTerms.intValue(); 
	}
	
	public boolean isSortFinitary(LeafExpression s)
	throws NotASortException
	{
		if(!sorts.contains(s))
			throw new NotASortException("isSortFinitary: LeafExpression "+s+" was not declared as a sort.");
		return finitarySorts.contains(s);
	}
	
	public void printInfo()
	{
		System.out.println(getInfoString());
	}
			
	public String getInfoString()
	{
		String eol = "\n";
		String boldOn = "";
		String boldOff = "";
		if(htmlOutput)
		{
			eol = "<BR>"+eol;
			boldOn = "<B>";
			boldOff = "</B>";
		}
		
		String result = "";
		
		if(sapConstants.size() > 0 || sapFunctions.size() > 0)
		{
			result += boldOn+"A sort symbol occured as a predicate. Setting for Sort-as-predicate handling was:" + boldOff+eol;
			if(sap.equals(EnumSAPHandling.sapKeep))
				result += "Keep."+eol;
			else if(sap.equals(EnumSAPHandling.sapIgnore))
				result += "Ignore. (Totals may be incorrect.)"+eol;
			else
				result += "Throw exception. (SAP would have caused an error; this should never be seen)."+eol;
			result += eol;
		}
		
		result += boldOn+"Constants (both original and Skolem):"+boldOff+eol;
		for(SigFunction c : skolemConstants)
			result += "  "+ c.toPrettyString() + ""+eol;
		for(SigFunction c : originalConstants)
			result += "  "+ c.toPrettyString() + ""+eol;
		
		if(sapConstants.size() > 0)
		{
			result += boldOn+"Coercions applied to individual constants due to sorts-as-predicates:"+boldOff+eol;
			for(SigFunction sc : sapConstants)
				result += "  "+ sc.toPrettyString() + ""+eol;
		}

		result += ""+eol;
		
		result += boldOn+"Functions (both original and Skolem): "+boldOff+eol;
		for(SigFunction f : skolemFunctions)
			result += "  "+ f.toPrettyString() +""+eol;
		for(SigFunction f : originalFunctions)
			result += "  "+ f.toPrettyString() +""+eol;
		if(skolemFunctions.size() + originalFunctions.size() < 1)
			result += "  (No non-nullary functions.)"+eol;
		
		if(sapFunctions.size() > 0)
		{
			result += boldOn+"Coercions due to sorts-as-predicates:"+boldOff+eol;
			for(SigFunction sf : sapFunctions)
				result += "  "+ sf.toPrettyString() + ""+eol;
		}
		
		// TODO distinction between finitary and finitary+populated?
		
		
		
		result += ""+eol;
		result += boldOn+"Functions that contribute to the count: "+boldOff+eol;
		for(SigFunction f : productiveFunctions)
			result += f.toPrettyString()+eol;
		if(productiveFunctions.size() == 0)
			result += "(None!)"+eol;
		if(productiveSAPFunctions.size() > 0)
		{
			result += boldOn+"Coercions due to sorts-as-predicates which contributed:"+boldOff+eol;
			for(SigFunction sf : productiveSAPFunctions)
				result += "  "+ sf.toPrettyString() + ""+eol;
		}
		
		
		result += eol;
		
		// infinitary sorts
		Set<LeafExpression> infSorts = new HashSet<LeafExpression>(sorts);
		infSorts.removeAll(finitarySorts);		
		
		result += boldOn+"Finitary sorts:"+boldOff+eol + finitarySorts.toString()+""+eol; 
		result += boldOn+"Infinitary sorts:"+boldOff+eol + infSorts.toString()+""+eol;
			
		result += ""+eol; 
		
		String sPopTermCounts = "";
		for(LeafExpression r : termCounts.keySet())
		{
			if(termCounts.get(r).intValue() > 0)
				sPopTermCounts += r.name() + ": " + termCounts.get(r).intValue() + " ";
		}
		
		if(htmlOutput)		
			result += "<HR><div style=\"text-align:center\">\n";
		
		if(termCounts.keySet().size() > 0)
			result += "Counts for finitary, populated sorts: "+boldOn+sPopTermCounts+boldOff+eol;
		
		Set<LeafExpression> unpopulatedSorts = new HashSet<LeafExpression>();
		for(LeafExpression r : finitarySorts)
		{
			if(!termCounts.containsKey(r) || termCounts.get(r).intValue() == 0)
				unpopulatedSorts.add(r);

		}
		if(unpopulatedSorts.size() > 0)
			result += "The following sorts were finitary but unpopulated by ground terms: "+unpopulatedSorts + ""+eol;
		if(getTermCount() > 0)
			result += "Number of "+boldOn+"distinct"+boldOff+" terms across all finitary sorts: "+boldOn+getTermCount()+boldOff+eol;
		else
			result += "All sorts were either infinitary or unpopulated."+eol; 
		

		if(htmlOutput)
			result += "<HR>\n";
		result += eol;
		
		// Docs: "Expresses a value in megaCycles as its approximate equivalent
		//        of CPU seconds on a theoretical 1.2 GHz CPU. "
		// For now, just print megacycles. Better than nothing?
		// not really. all zero even if supports is true. Disabling for now.
		//double msCollect = qs.convertMegacyclesToCpuSeconds(mCycCollect) * 1000;
		//double msProductive = qs.convertMegacyclesToCpuSeconds(mCycProductive) * 1000;
		//double msFinitary = qs.convertMegacyclesToCpuSeconds(mCycFinitary) * 1000;
		//double msBounds = qs.convertMegacyclesToCpuSeconds(mCycBounds) * 1000;
		if(!htmlOutput)
		{
			result += "Time to collect Skolem functions: "+msCollect +eol;
			result += "Time to identify productive functions: "+msProductive +eol;
			result += "Time to identify finitary sorts: "+msFinitary +eol;
			result += "Time to calculate number of terms: "+msBounds +eol;
				
		result += "-----------------------------------"+eol;
		}
		return result;
	}	
	
}

