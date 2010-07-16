package edu.wpi.termcount;

import java.util.HashSet;
import java.util.Set;

import kodkod.ast.visitor.*;
import kodkod.ast.*;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Quantifier;

class NNFConverterV extends AbstractReplacer 
{
	public NNFConverterV()
	{
		super(new HashSet<Node>());		
	}
	
	static private void runUnitTest(NNFConverterV conv, Formula pre, Formula post)
	{
		//if(!pre.accept(conv).equals(post))
		if(!pre.accept(conv).toString().equals(post.toString()))
			System.out.println("Error: Expected "+post.toString()+", got: "+pre.accept(conv).toString());	
	}
	
	static public void unitTest()
	{
		// *********************************
		// Tests for NNF conversion go here.
		// *********************************
		
		System.out.println("----- Begin NNFConverterV Tests (No messages is good.) -----");
		
		NNFConverterV conv = new NNFConverterV();		
		
		// Test conversion of basic constant formulas
		runUnitTest(conv, Formula.TRUE.not(), Formula.FALSE);
		runUnitTest(conv, Formula.FALSE.not(), Formula.TRUE);
				
		Variable x = MFormulaManager.makeVariable("x");
		Variable y = MFormulaManager.makeVariable("y");
		Relation P = MFormulaManager.makeRelation("P", 1);
		
		// Test double-negation removal.
		runUnitTest(conv, Formula.TRUE.not().not(), Formula.TRUE);
		runUnitTest(conv, x.in(P).not().not(), x.in(P));		
		runUnitTest(conv, x.in(P).not().not().and(x.in(P)), x.in(P).and(x.in(P)));

		// De Morgan
		runUnitTest(conv, x.in(P).or(y.in(P)).not(), x.in(P).not().and(y.in(P).not()));
		runUnitTest(conv, x.in(P).and(y.in(P)).not(), x.in(P).not().or(y.in(P).not()));
		
		// De Morgan & double-negation
		runUnitTest(conv, x.in(P).or(x.in(P).not().not()).not().not().not(), x.in(P).not().and(x.in(P).not()));
		
		// Nested De Morgan
		runUnitTest(conv, x.in(P).or(x.in(P)).not().or(x.in(P)), x.in(P).not().and(x.in(P).not()).or(x.in(P)));
		runUnitTest(conv, x.in(P).or(x.in(P)).not().or(x.in(P)).not(), x.in(P).or(x.in(P)).and(x.in(P).not()));
		
		// No change
		runUnitTest(conv, x.in(P).and(x.in(P).not()), x.in(P).and(x.in(P).not()));		
		
		// Need to test IMPLIES, IFF, and XOR in **and** outside the context of a negation.
		// (The code contains separate sections for these cases.)
		
		// IMP/IFF/XOR without negation outside
		runUnitTest(conv, x.in(P).implies(y.in(P)), x.in(P).not().or(y.in(P)));
		runUnitTest(conv, x.in(P).iff(y.in(P)), x.in(P).and(y.in(P)).or(y.in(P).not().and(x.in(P).not())));
		
		// IMP/IFF/XOR with negation outside
		runUnitTest(conv, x.in(P).implies(y.in(P)).not(), x.in(P).and(y.in(P).not()));
		runUnitTest(conv, x.in(P).iff(y.in(P)).not(), x.in(P).and(y.in(P).not()).or(y.in(P).and(x.in(P).not())));
		
		// Quantifiers
		Decl xd = x.oneOf(Expression.UNIV);
		Decl yd = y.oneOf(Expression.UNIV);
		
		runUnitTest(conv, x.in(P).forSome(xd).not(), x.in(P).not().forAll(xd));
		runUnitTest(conv, x.in(P).forAll(xd).not(), x.in(P).not().forSome(xd));
		runUnitTest(conv, x.in(P).and(y.in(P)).forSome(yd).forSome(xd).not(), 
				          x.in(P).not().or(y.in(P).not()).forAll(yd).forAll(xd));
		// Nested quantifiers
		
		//runUnitTest(conv, , );
		
		Set<Formula> testset = new HashSet<Formula>();
		Relation r1 = Relation.unary("r1");
		Relation r2 = Relation.unary("r2");
		Relation r3 = Relation.unary("r3");
		Relation r4 = Relation.unary("r4");
		Relation r5 = Relation.unary("r5");
		Relation r6 = Relation.unary("r6");
		
		// NaryFormulas
		testset.add(x.in(r1));
		testset.add(x.in(r2));
		testset.add(x.in(r3));
		testset.add(x.in(r4));
		testset.add(x.in(r5));
		testset.add(x.in(r6));
		Formula bar = Formula.and(testset).not();
		
		testset.clear();
		testset.add(x.in(r1).not());
		testset.add(x.in(r2).not());
		testset.add(x.in(r3).not());
		testset.add(x.in(r4).not());
		testset.add(x.in(r5).not());
		testset.add(x.in(r6).not());
				
		runUnitTest(conv, bar, Formula.or(testset));
		
		System.out.println("----- End NNFConverterV Tests -----");
	}
		
	public Formula visit(NaryFormula bf)
	{
		// Only AND and OR (see BinaryFormula case)
		if(cache.containsKey(bf))
			return lookup(bf);
		
		cached.add(bf);
		
		// The result will be the newformulas composed with op.
		Set<Formula> newformulas = new HashSet<Formula>();
		for(Formula fmla : bf)
			newformulas.add(fmla.accept(this));

		if(!bf.op().equals(FormulaOperator.AND) && !bf.op().equals(FormulaOperator.OR))
		{
			System.err.println("Warning: NaryFormula operator "+bf.op() +" not supported.");
			System.exit(1);
		}

		try
		{
			return cache(bf, MFormulaManager.makeComposition(bf.op(), newformulas));
		}
		catch(MGEManagerException e)
		{		
			System.err.println(e);
			System.exit(1);
			return bf; // never reached
		}
	}
	
	
	public Formula visit(BinaryFormula bf)
	{
		// Only AND and OR allowed as binary connectives in NNF formulas.

		// Verbose "newleft" and "newright" code below is to make what's happening clear.
		// The .accept(this) calls make everything ugly if contained on a single line.
		
		if(cache.containsKey(bf))
			return lookup(bf);
		
		cached.add(bf);
		
		Formula newleft, newright;		
		
		switch(bf.op())
		{
			case AND:
				newleft = bf.left().accept(this);
				newright = bf.right().accept(this);
				return cache(bf, MFormulaManager.makeAnd(newleft, newright));
				
			case OR:
				newleft = bf.left().accept(this);
				newright = bf.right().accept(this);
				return cache(bf, MFormulaManager.makeOr(newleft, newright));
			
			// !a or b				
			case IMPLIES: 
				newleft = MFormulaManager.makeNegation(bf.left()).accept(this);
				newright = bf.right().accept(this);
				return cache(bf, MFormulaManager.makeOr(newleft, newright)); 
			
			// (a and b) or (!a and !b)
			case IFF:
				newleft = MFormulaManager.makeAnd(bf.left(), bf.right()).accept(this);
				newright = MFormulaManager.makeAnd(MFormulaManager.makeNegation(bf.right()), 
						                            MFormulaManager.makeNegation(bf.left())).accept(this);
				return cache(bf, MFormulaManager.makeOr(newleft, newright));
					
			// Everything else, do nothing!
			default:
				newleft = bf.left().accept(this);
				newright = bf.right().accept(this);
				cached.add(bf);
				return cache(bf, newleft.compose(bf.op(), newright));		
		}
	}
	
	
	public Formula visit(NotFormula nf)
	{
		// Negations must be in front of ground statements.
		// See above visitor for verbose code rationale.

		if(cache.containsKey(nf))
			return lookup(nf);
		
		cached.add(nf);
		
		Formula newleft, newright, negleft, negright;
		
		if(nf.formula() instanceof NotFormula)
		{			
			// If this negation is immediately cancelled
			return cache(nf, ((NotFormula)nf.formula()).formula().accept(this));
			// (No addition to negFormulas.)
		}		
				
		if(nf.formula() instanceof NaryFormula)
		{
			NaryFormula within = (NaryFormula)nf.formula();
			Set<Formula> newformulas = new HashSet<Formula>();
			
			for(Formula fmla : within)
			{
				Formula negfmla = MFormulaManager.makeNegation(fmla);
				newformulas.add(negfmla.accept(this));
				
				// each stage of pushing down the not gets cached
				// and stored by the manager. that is bad.
				
				// Possible to optimize out some of this time? TODO
				
			}				
			
			// De Morgan's law:
			switch(within.op())
			{
				case AND:
					return cache(nf, MFormulaManager.makeDisjunction(newformulas));
				case OR:
					return cache(nf, MFormulaManager.makeConjunction(newformulas));
				default:
					System.err.println("Warning: NaryFormula operator "+within.op() +" not supported.");
					System.exit(1);					
			}
		}
		
		if(nf.formula() instanceof BinaryFormula)
		{
			BinaryFormula within = (BinaryFormula)nf.formula();
			negleft = MFormulaManager.makeNegation(within.left());
			negright = MFormulaManager.makeNegation(within.right());
			
			switch(within.op())
			{
				// Normal cases. Apply De Morgan's and revisit.
				case AND: 
					newleft = negleft.accept(this);					
					newright = negright.accept(this);
					return cache(nf, MFormulaManager.makeOr(newleft, newright));
					
				case OR:
					newleft = negleft.accept(this);					
					newright = negright.accept(this);
					return cache(nf, MFormulaManager.makeAnd(newleft, newright));
				
				// a and !b				
				case IMPLIES:
					newleft = within.left().accept(this);
					newright = negright.accept(this);
					return cache(nf, MFormulaManager.makeAnd(newleft, newright)); 
				
				// (a and !b) or (b and !a)
				case IFF: 
					newleft = MFormulaManager.makeAnd(within.left(), negright).accept(this);
					newright = MFormulaManager.makeAnd(within.right(), negleft).accept(this);
					return cache(nf, MFormulaManager.makeOr(newleft, newright));
					
			}
		}
		
		if(nf.formula() instanceof ConstantFormula)
		{
			// Flip the constant
			ConstantFormula within = (ConstantFormula)nf.formula();
			if(within.booleanValue()) return cache(nf, Formula.FALSE);
			else return cache(nf, Formula.TRUE);
		}
		
		if(nf.formula() instanceof ComparisonFormula)
		{		
			// Of the form Expression = Expression 
			// or          Expression in Expression
			// Thus the negation is at "bottom" in the formula.
			cache(nf.formula(), nf.formula());
			return cache(nf, nf);
		}
		
		if(nf.formula() instanceof IntComparisonFormula)
		{			
			// Not supported. Better as an exception... add later?
			System.out.println("Warning: Unexpected formula type when converting to NNF.");
			return cache(nf, nf);
		}
		if(nf.formula() instanceof MultiplicityFormula)
		{		
			// Of the form Expression. (lone, no, one, set, or some)
			// The negation is at the "bottom" in the formula.
			return cache(nf, nf);
		}
		if(nf.formula() instanceof QuantifiedFormula)
		{
			// Distribute the negation through the quantifier.
			// (This works fine in sorted logic.)
			QuantifiedFormula within = (QuantifiedFormula)nf.formula();
			Formula negwithin = MFormulaManager.makeNegation(within.formula());
			Formula newinsidewithin = negwithin.accept(this);		
			
			try
			{
			
				if(within.quantifier().equals(Quantifier.ALL))
					return cache(nf, MFormulaManager.makeExists(newinsidewithin, within.decls())); //newinsidewithin.forSome(within.decls()));

				// must be an existential, then 			
				return cache(nf, MFormulaManager.makeForAll(newinsidewithin, within.decls()));
			}
			catch(MGEManagerException e)
			{
				System.err.println(e);
								
				// don't use manager
				if(within.quantifier().equals(Quantifier.ALL))
					return cache(nf, newinsidewithin.forSome(within.decls())); 
				return cache(nf, newinsidewithin.forAll(within.decls()));
			}

			
		}
		if(nf.formula() instanceof RelationPredicate)
		{
			// Not supported. Better as an exception... add later?
			System.out.println("Warning: Unexpected formula type when converting to NNF.");

			return cache(nf, nf);
		}
		
		System.out.println("Warning: Unexpected formula type when converting to NNF.");
		return cache(nf, nf);
		
	} // end visit(NotFormula)
		
	public Formula visit(ComparisonFormula comp)
	{
		// Ground formulas remain the same
		if(cache.containsKey(comp))
			return lookup(comp);
		cached.add(comp);
		return cache(comp, comp);
	}
}
