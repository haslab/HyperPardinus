/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.test.pardinus.decomp;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.BeforeClass;
import org.junit.Test;

/**
 * Basic tests to check whether the temporal bounded engine is running with the decomposed strategy.
 * 
 * @author Nuno Macedo // [HASLab] temporal, decomposed, unbounded model finding
 */
public class BaseTests {
	private static PardinusSolver dsolver;
	private static ExtendedOptions opt;

	@BeforeClass
	public static void method() throws InterruptedException {
		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setRunDecomposed(true);
		opt.setRunTemporal(false);
//		opt.setReporter(new SLF4JReporter());
		opt.configOptions().setReporter(opt.reporter());
	}

	@Test
	public void testSAT() {
		opt.setSolver(SATFactory.DEFAULT);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds2.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.eq(c).not()); // never trivial
		
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol = null;
		for (int i = 0; i < 13; i++) {
			if (sols.hasNext())
				sol = sols.next();
			if (sol.unsat()) 
				sol = sols.nextC();
			opt.reporter().debug("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialConfig() {
		opt.setSolver(SATFactory.DEFAULT);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.in(b).and(b.eq(c).not()); // config trivial
		
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol = null;
		for (int i = 0; i < 15; i++) {
			if (sols.hasNext()) {
				sol = sols.next();
			}
			if (sol.unsat()) {
				sol = sols.nextC();
			}
			opt.reporter().debug("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialRem() {
		opt.setSolver(SATFactory.DEFAULT);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)); // all remainder trivial
		
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol = null;
		for (int i = 0; i < 18; i++) {
			if (sols.hasNext())
				sol = sols.next();
			if (sol.unsat()) 
				sol = sols.nextC();
			opt.reporter().debug("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialSomeRem() {
		opt.setSolver(SATFactory.DEFAULT);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds2.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.in(c)); // some remainder trivial
		
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol = null;
		for (int i = 0; i < 9; i++) {
			if (sols.hasNext())
				sol = sols.next();
			if (sol.unsat()) 
				sol = sols.nextC();
			opt.reporter().debug("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());

		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSAT2() {
		opt.setSolver(SATFactory.DEFAULT);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.eq(c).not()); // never trivial
		
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol = null;
		for (int i = 0; i < 13; i++) {
			if (sols.hasNext())
				sol = sols.next();
			if (sol.unsat()) 
				sol = sols.nextC();
			opt.reporter().debug("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
}
