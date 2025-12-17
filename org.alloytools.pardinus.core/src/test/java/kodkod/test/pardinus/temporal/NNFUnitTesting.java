package kodkod.test.pardinus.temporal;

import kodkod.ast.*;
import kodkod.engine.ltl2fol.NNFReplacer;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * Tests whether the conversion into negated normal form is correct.
 * 
 * As of Pardinus 1.1 traces are assumed to be infinite and NNF no longer
 * required.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class NNFUnitTesting {

	private static Relation A = Relation.unary_variable("A");
	private static Relation B = Relation.unary_variable("B");
	private static Relation C = Relation.binary_variable("C");
	private static Relation toSend = Relation.binary_variable("toSend");
	private static Relation Process = Relation.unary("Process");

	@Test
	public final void test1() {
		Formula initial = A.lone().implies(B.some());
		Formula result = (A.lone().not()).or(B.some());
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test2() {
		Formula initial = A.lone().implies(B.some()).not();
		Formula result = (A.lone()).and(B.some().not());
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test3() {
		Formula initial = Formula.TRUE.iff(B.some());
		Formula result = (Formula.TRUE.or(B.some().not())).and((Formula.FALSE.not()).or(B.some()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test4() {
		Formula initial = A.lone().iff(B.some()).not();
		Formula result = ((A.lone().not()).and(B.some())).or((A.lone()).and(B.some().not()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test5() {
		Formula initial = A.some().not().not().and(B.lone()).not();
		Formula result = (A.some().not()).or(B.lone().not());
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test6() {
		Formula initial = A.some().or(B.lone()).not();
		Formula result = (A.some().not()).and(B.lone().not());
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test7() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).forAll(v.oneOf(A)).not();
		Formula result = (C.join(v).some().not()).or(B.lone().not()).forSome(v.oneOf(A));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test8() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).forSome(v.oneOf(A)).not();
		Formula result = (C.join(v).some().not()).and(B.lone().not()).forAll(v.oneOf(A));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test9() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).always().not();
		Formula result = (C.join(v).some().not()).and(B.lone().not()).eventually();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test10() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).eventually().not();
		Formula result = (C.join(v).some().not()).or(B.lone().not()).always();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test11() {
		Formula initial = A.some().and(A.some().implies(B.one())).not();
		Formula result = A.some().not().or(A.some().and(B.one().not()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test12() {
		Formula initial = A.some().and(A.some().implies(B.one()).not()).not();
		Formula result = A.some().not().or(A.some().not().or(B.one()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test13() {
		Formula initial = A.some().and(A.some().not().implies(B.one()).not()).not();
		Formula result = A.some().not().or(A.some().or(B.one()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test14() {
		Formula initial = A.some().or(A.some().not().implies(B.one()).not()).not();
		Formula result = A.some().not().and(A.some().or(B.one()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test15() {
		Formula initial = A.some().and(A.some().implies(B.one()).not());
		Formula result = A.some().and(A.some().and(B.one().not()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test16() {
		Formula initial = A.some().implies(B.one()).not().implies(A.some().implies(B.one()).not());
		Formula result = A.some().not().or(B.one()).or(A.some().and(B.one().not()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test17() {
		Formula initial = A.some().or(A.some().implies(B.one())).not();
		Formula result = A.some().not().and(A.some().and(B.one().not()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test18() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().not().and(B.lone()).forSome(v.oneOf(A)).not();
		Formula result = C.join(v).some().or(B.lone().not()).forAll(v.oneOf(A));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test19() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forSome(v.oneOf(A)).not().iff(C.join(v).lone());
		Formula result = C.join(v).some().not().forAll(v.oneOf(A)).or(C.join(v).lone().not())
				.and(C.join(v).some().forSome(v.oneOf(A)).or(C.join(v).lone()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test20() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forAll(v.oneOf(A)).always().not().iff(C.join(v).lone());
		Formula result = C.join(v).some().not().forSome(v.oneOf(A)).eventually().or(C.join(v).lone().not())
				.and(C.join(v).some().forAll(v.oneOf(A)).always().or(C.join(v).lone()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test21() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().always().forAll(v.oneOf(A)).not();
		Formula result = C.join(v).some().not().eventually().forSome(v.oneOf(A));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test22() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).once().not();
		Formula result = C.join(v).some().not().or(B.lone().not()).historically();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test23() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forAll(v.oneOf(A)).historically().not().iff(C.join(v).lone());
		Formula result = C.join(v).some().not().forSome(v.oneOf(A)).once().or(C.join(v).lone().not())
				.and(C.join(v).some().forAll(v.oneOf(A)).historically().or(C.join(v).lone()));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test24() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().historically().forAll(v.oneOf(A)).not();
		Formula result = C.join(v).some().not().once().forSome(v.oneOf(A));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test25() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).once().not();
		Formula result = C.join(v).some().not().and(B.lone().not()).historically();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test26() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).after().not();
		Formula result = C.join(v).some().not().and(B.lone().not()).after();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test27() {
		Variable v = Variable.unary("v");
		Formula initial = Formula
				.and(new Formula[] { C.join(v).some().or(B.lone()).after(), A.lone().implies(B.some()), B.lone().not() })
				.not();
		Formula result = Formula.or(new Formula[] { C.join(v).some().not().and(B.lone().not()).after(),
				A.lone().and(B.some().not()), B.lone() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test28() {
		Variable v = Variable.unary("v");
		Formula initial = Formula
				.and(new Formula[] { C.join(v).some().or(B.lone()).after(), A.lone().implies(B.some()), B.lone() })
				.not();
		Formula result = Formula.or(new Formula[] { C.join(v).some().not().and(B.lone().not()).after(),
				A.lone().and(B.some().not()), B.lone().not() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test29() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(new Formula[] { C.join(v).some().and(B.prime().lone()).after().not(),
				A.lone().implies(B.some()), B.lone().not() }).not();
		Formula result = Formula.or(new Formula[] { C.join(v).some().and(B.prime().lone()).after(),
				A.lone().and(B.some().not()), B.lone() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test30() {
		Variable v = Variable.unary("v");
		Formula initial = Formula
				.and(new Formula[] { C.join(v).some().and(B.lone()).after(), A.lone().implies(B.some()), B.lone() })
				.not();
		Formula result = Formula.or(new Formula[] { C.join(v).some().not().or(B.lone().not()).after(),
				A.lone().and(B.some().not()), B.lone().not() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test31() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.or(new Formula[] { C.join(v).some().and(B.lone()).always().eventually(),
				A.lone().not().implies(B.some()), B.lone() }).not();
		Formula result = Formula.and(new Formula[] { C.join(v).some().not().or(B.lone().not()).eventually().always(),
				A.lone().not().and(B.some().not()), B.lone().not() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test32() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).always().before().not();
		Formula result = C.join(v).some().not().and(B.lone().not()).eventually().before();
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test33() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(
				new Formula[] { C.join(v).some().or(B.lone()).before(), A.lone().implies(B.some()), B.lone().not() })
				.not();
		Formula result = Formula.or(new Formula[] { C.join(v).some().not().and(B.lone().not()).before(),
				A.lone().and(B.some().not()), B.lone() });
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test34() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).not();
		String result = "(some p: one Process | (!((toSend . p) = (toSend . p)) releases !lone (Process . toSend')))";
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test35() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).not();
		Formula result = toSend.join(var3).eq(toSend.join(var3)).not()
				.releases(Process.join(toSend.prime()).lone().not()).forSome(var3.oneOf(Process));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test36() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).and(Process.join(toSend.prime()).one())
				.releases(Process.join(toSend.prime()).lone()).forAll(var3.oneOf(Process)).not();
		Formula result = toSend.join(var3).eq(toSend.join(var3)).not().or(Process.join(toSend.prime()).one().not())
				.releases(Process.join(toSend.prime()).lone().not()).forSome(var3.oneOf(Process));
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	@Test
	public final void test37() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).and(Process.join(toSend.prime()).one())
				.until(Process.join(toSend.prime()).lone()).not();
		Formula result = toSend.join(var3).eq(toSend.join(var3)).not().or(Process.join(toSend.prime()).one().not())
				.until(Process.join(toSend.prime()).lone().not());
		assertEquals(NNFReplacer.nnf(initial).toString(), result.toString());
	}

	public static void p(String s) {
		System.out.println(s);
	}

}
