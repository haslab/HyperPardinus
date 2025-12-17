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
package kodkod.test.pardinus.symbolic;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.engine.config.SLF4JReporter;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Tests symbolic bound resolution.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class ResolutionTests {

	Relation r,s,t,u;
	Relation a,b,c,d;
	Universe uni;
	TupleSet as, bs, a0, b0;
	
	@Before 
	public void setup() {
		r = Relation.binary("r");
		s = Relation.binary_variable("s");
		t = Relation.nary("t", 3);
		u = Relation.variable("u", 3);
		
		a = Relation.unary("a");
		b = Relation.unary_variable("b");
		c = Relation.unary("c");
		d = Relation.unary_variable("d");
		
		int n = 3;
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));
		a0 = f.setOf("A0");
		b0 = f.setOf("B0");
	}
	
	@Test
	public void test1() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		// a :1 {} {A0,...,An}
		bnds.bound(a, as);
		// var b :1 NONE a
		bnds.bound(b, Expression.NONE, a);
		// c :1 (b + {A0}) b
		bnds.bound(c, b.union(bnds.reify(a0)), b);
		// var d :1 NONE c
		bnds.bound(d, c);
		
		// r :2 (a -> a) (a -> a)
		bnds.bound(r, a.product(a), a.product(a));
		// var s :2 (a -> NONE) (a -> {B0,...,Bn})
		bnds.bound(s, a.product(Expression.NONE), a.product(bnds.reify(bs)));
		// t :3 ({A0} -> {A0} -> {A0}) (a -> b -> c)
		bnds.bound(t, bnds.reify(a0).product(bnds.reify(a0)).product(bnds.reify(a0)), a.product(b).product(c));
		// var u :3 (r -> {A0}) (r -> b)
		bnds.bound(u, r.product(bnds.reify(a0)), r.product(b));
		
		Formula f = bnds.resolve(new SLF4JReporter());
	
		PardinusBounds oracle = new PardinusBounds(uni);
		// a :1 {} {A0,...,An}
		oracle.bound(a, as);
		// var b :1 {} {A0,...,An} 								* b in a
		oracle.bound(b, as);	
		// c :1 {A0} {A0,...,An} 								* b + {A0} in c && c in b
		oracle.bound(c, a0, as);
		// var d :1 {} {A0,...,An} 								* d in c
		oracle.bound(d, as);
		// r :2 {} {(A0,A0),...(An,An)} 						* a -> a in r && r in a -> a
		oracle.bound(r, as.product(as));
		// var s :2 {} {(A0,B0),...(An,Bn)}						* s in a -> {B0,...,Bn}
		oracle.bound(s, as.product(bs));
		// t :3 {(A0,A0,A0)} {(A0,A0,A0),...,(An,An,An)}		* t in a -> b -> c
		oracle.bound(t, a0.product(a0).product(a0), as.product(as).product(as));
		// var u :3 {} {(A0,A0,A0),...,(An,An,An)}				* r -> {A0} in u && u in (r -> b)
		oracle.bound(u, as.product(as).product(as));

		assertTrue(compare(bnds,oracle));

		Formula f1 = b.in(a);
		Formula f2 = (b.union(((bnds.reify(a0)))).in(c)).and(c.in(b));
		Formula f3 = t.in((a.product(b)).product(c));
		Formula f4 = ((a.product(a)).in(r)).and(r.in(a.product(a)));
		Formula f5 = ((r.product((bnds.reify(a0)))).in(u)).and(u.in(r.product(b)));
		Formula f6 = s.in(a.product((((bnds.reify(bs))))));
		Formula f7 = d.in(c);
		Formula xtra = NaryFormula.and(f1.always(),f2.always(),f3.always(),f4,f5.always(),f6.always(),f7.always());
		assertEquals(f.toString().length(), xtra.toString().length());
	}
	
	@Test
	public void test1a() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		// a :1 {A0,...,An} {A0,...,An}
		bnds.boundExactly(a, as);
		// var b :1 {A0,...,An} a
		bnds.bound(b, bnds.reify(as), a);
		// c :1 (b + {A0}) b
		bnds.bound(c, b.union(bnds.reify(a0)), b);
		// var d :1 NONE c
		bnds.bound(d, c);
		
		// r :2 (a -> a) (a -> a)
		bnds.bound(r, a.product(a), a.product(a));
		// var s :2 (a -> NONE) (a -> {B0,...,Bn})
		bnds.bound(s, a.product(Expression.NONE), a.product(bnds.reify(bs)));
		// t :3 ({A0} -> {A0} -> {A0}) (a -> b -> c)
		bnds.bound(t, bnds.reify(a0).product(bnds.reify(a0)).product(bnds.reify(a0)), a.product(b).product(c));
		// var u :3 (r -> {A0}) (r -> b)
		bnds.bound(u, r.product(bnds.reify(a0)), r.product(b));
		
		Formula f = bnds.resolve(new SLF4JReporter());
	
		PardinusBounds oracle = new PardinusBounds(uni);
		// a :1 {A0,...,An} {A0,...,An}
		oracle.boundExactly(a, as);
		// var b :1 {A0,...,An} {A0,...,An} 
		oracle.boundExactly(b, as);	
		// c :1  {A0,...,An} {A0,...,An} 
		oracle.bound(c, as, as);
		// var d :1 {} {A0,...,An} 								
		oracle.bound(d, as);
		// r :2 {(A0,A0),...(An,An)} {(A0,A0),...(An,An)} 
		oracle.boundExactly(r, as.product(as));
		// var s :2 {} {(A0,B0),...(An,Bn)}	
		oracle.bound(s, as.product(bs));
		// t :3 {(A0,A0,A0)} {(A0,A0,A0),...,(An,An,An)}
		oracle.bound(t, a0.product(a0).product(a0), as.product(as).product(as));
		// var u :3 {(A0,A0,A0),...,(An,An,A0)} {(A0,A0,A0),...,(An,An,An)}				
		oracle.bound(u, as.product(as).product(a0), as.product(as).product(as));

		assertTrue(compare(bnds,oracle));

		Formula xtra = NaryFormula.and();
		assertEquals(f.toString().length(), xtra.toString().length());
	}
	
	@Test
	public void test2() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		// a :1 {} {A0,...,An}
		bnds.bound(a, as);
		// var b :1 {} (a + {B0})
		bnds.bound(b, a.union(bnds.reify(b0)));
		// c :1 {B0,...,Bn} {B0,...,Bn}
		bnds.bound(c, bs, bs);
		// var d :1 {} c + b
		bnds.bound(d, c.union(b));
		
		// r :2 (c -> c + a -> a) (c -> {B0,...,Bn} + a -> a)
		bnds.bound(r, (c.product(c)).union(a.product(a)), (c.product(bnds.reify(bs))).union(a.product(a)));
		// var s :2 {(B0,A0)} {(B0,A0),...,(Bn,An)}
		bnds.bound(s, b0.product(a0), bs.product(as));
		// t :3 (s -> {(B0,...,Bn)}) (s -> {(B0,...,Bn)})
		bnds.bound(t, s.product(bnds.reify(bs)), s.product(bnds.reify(bs)));
		
		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		// a :1 {} {A0,...,An}									
		orcl.bound(a, as);
		TupleSet x = as.clone();
		x.addAll(b0);
		// var b :1 {} {A0,...,An,B0}												* b in a + {B0}
		orcl.bound(b, x);
		// c :1 {B0,...,Bn} {B0,...,Bn}
		orcl.bound(c, bs, bs);
		x.addAll(bs);
		// var d :1 {} {A0,...,An,B0,...,Bn} 										* d in c + b
		orcl.bound(d, x);
		x = (as.product(as)).clone();
		x.addAll(bs.product(bs));
		// r :2 {(B0,B0),...,(Bn,Bn)} {(A0,A0),...,(An,An),(B0,B0),...,(Bn,Bn)} 	* (c -> c + a -> a) in r && r in (c -> {B0,...,Bn} + a -> a)
		orcl.bound(r, bs.product(bs), x);
		// var s :2 {(B0,A0)} {(B0,A0),...,(Bn,An)}
		orcl.bound(s, b0.product(a0), bs.product(as));
		// t :3 {(B0,A0,B0),...,(B0,A0,Bn))} {(B0,A0,B0),...,(Bn,An,Bn))}			* (s -> {(B0,...,Bn)}) in t && t in (s -> {(B0,...,Bn)})
		orcl.bound(t, b0.product(a0).product(bs), bs.product(as).product(bs));

		assertTrue(compare(bnds,orcl));
		
		Formula f1 = b.in(a.union(bnds.reify(b0)));
		Formula f2 = d.in(c.union(b));
		Formula f3 = (c.product(c)).union(a.product(a)).in(r).and(r.in((c.product(bnds.reify(bs))).union(a.product(a))));
		Formula f4 = (s.product(bnds.reify(bs))).in(t).and(t.in(s.product(bnds.reify(bs))));
		Formula xtra = NaryFormula.and(f1.always(),f2.always(),f3,f4.always());
		assertEquals(f.toString().length(), xtra.toString().length());

	}
	
	// known bug in "difference" expressions
	@Test
	public void test3() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		// a :1 {} {A0,...,An}
		bnds.bound(a, as);
		// b :1 {} {A0,...,An}
		bnds.bound(b, as);
		// c :1 {} a-b
		bnds.bound(c, a.difference(b));
		
		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		// a :1 {} {A0,...,An}
		orcl.bound(a, as);
		// b :1 {} {A0,...,An}
		orcl.bound(b, as);
		// c :1 {} {A0,...,An}
		orcl.bound(c, as);

		assertTrue(compare(bnds,orcl));
	}
	
	// known bug in static with variable bounds
	@Test
	public void test5() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		// var s :1 {} {(A0,A0),...,(An,An)}
		bnds.bound(s, as.product(as));
		// r :1 {} s
		bnds.bound(r, s);

		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		// var s :1 {} {(A0,A0),...,(An,An)}
		orcl.bound(s, as.product(as));
		// r :1 {} {(A0,A0),...,(An,An)}
		orcl.bound(r, as.product(as));

		assertTrue(compare(bnds,orcl));
		
		assertEquals(f.toString().length(), r.in(s).always().toString().length());
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void test4() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		bnds.bound(a, as, as);
		bnds.bound(b, bs, bs);
		bnds.bound(c, a, b);
		
		Formula f = bnds.resolve(new SLF4JReporter());

	}
	
	private boolean compare(Bounds b1, Bounds b2) {
		for (Relation r : b1.relations()) {
			if (b1.lowerBound(r).size() != b2.lowerBound(r).size()) return false;
			if (b1.upperBound(r).size() != b2.upperBound(r).size()) return false;
		}
		return true;
	}

}
