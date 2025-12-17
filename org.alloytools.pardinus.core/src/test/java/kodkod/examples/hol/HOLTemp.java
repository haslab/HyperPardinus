/**
 *
 */
package kodkod.examples.hol;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.HOLSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 *
 * open util/ordering[Time] as t
 *
 * sig Val {} sig Time {}
 *
 * let nxt = t/next + t/last->Loop
 *
 * one sig Loop in Time {}
 *
 * abstract sig Proc {
 *  inv : Val one -> Time,
 *  ouv: Val one -> Time,
 *  nin: set Time }
 *
 * one sig A,B extends Proc {}
 *
 * fact {
 *  no nin.first
 *  all t:Time {
 *      all x:A+B | pub[x.inv,x.ouv,x.nin,t] or sec[x.inv,x.ouv,x.nin,t] or nop[x.inv,x.ouv,x.nin,t]
 *      pub[A.inv,A.ouv,A.nin,t] iff pub[B.inv,B.ouv,B.nin,t]
 *      all x:A+B | some t1:t.*nxt | (pub[x.inv,x.ouv,x.nin,t1] or sec[x.inv,x.ouv,x.nin,t1]) }
 * }
 *
 * pred pub[x:Val->Time,y:Val->Time,z:set Time,t:Time] {
 *  t not in z
 *  t.nxt in z
 *  x.(t.nxt) = x.t }
 *
 *
 * pred sec[x:Val->Time,y:Val->Time,z:set Time,t:Time] {
 *  t in z
 *  t.nxt not in z
 *  y.(t.nxt) = y.t }
 *
 * pred nop[x:Val->Time,y:Val->Time,z:set Time,t:Time] {
 *  t in z iff t.nxt in z
 *  y.(t.nxt) = y.t
 *  x.(t.nxt) = x.t }
 *
 * fun public[x:Val->Time,y:Val->Time,z:set Time,t:Time] : one Val {
 *  y.t }
 *
 * fun secret[x:Val->Time,y:Val->Time,z:set Time,t:Time] : one Val {
 *  x.t }
 *
 * check {
 *  some x:Val one->Time,y:Val one->Time,z:set Time {
 *      t/first not in z
 *      all t:Time {
 *          pub[x,y,z,t] or sec[x,y,z,t] or nop[x,y,z,t]
 *          public[A.inv,A.ouv,A.nin,t] = public[x,y,z,t]
 *          secret[B.inv,B.ouv,B.nin,t] = secret[x,y,z,t] } }
 * } for 3 but 5 Time
 */

public class HOLTemp {

    static Relation val   = Relation.unary("Val");
    static Relation a     = Relation.unary("A");
    static Relation b     = Relation.unary("B");
    static Relation inv   = Relation.variable("inv", 2);
    static Relation ouv   = Relation.variable("ouv", 2);
    static Relation nin   = Relation.variable("nin", 1);

    public static void main(String args[]) {

        int nv = 6, nt = 5;

        List<String> atomlist = new ArrayList<String>(Arrays.asList("A$0", "B$0", "t/Ord$0"));
        for (int i = 0; i < nv; i++) {
            atomlist.add("Val$"+i);
        }

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        PardinusBounds bounds = new PardinusBounds(universe);

        TupleSet vals_bound = factory.range(factory.tuple("Val$0"), factory.tuple("Val$"+(nv-1)));

        bounds.bound(val, vals_bound);

        TupleSet x8_upper = factory.setOf(factory.tuple("A$0"));
        bounds.boundExactly(a, x8_upper);

        TupleSet x9_upper = factory.setOf(factory.tuple("B$0"));
        bounds.boundExactly(b, x9_upper);

        TupleSet x12_upper = factory.noneOf(2);
        x12_upper.addAll(x8_upper.product(vals_bound));
        x12_upper.addAll(x9_upper.product(vals_bound));
        bounds.bound(inv, x12_upper);
        bounds.bound(ouv, x12_upper);

        TupleSet x14_upper = factory.noneOf(1);
        x14_upper.addAll(x8_upper);
        x14_upper.addAll(x9_upper);
        bounds.bound(nin, x14_upper);

        Formula a_disj_b = a.intersection(b).no();

        Expression proc = a.union(b);

        Variable this_p1 = Variable.unary("this");
        Expression this_inv = this_p1.join(inv);
        Variable v0 = Variable.unary("v0");
        Formula x28 = (this_inv.in(val).and(this_inv.one())).forAll(v0.oneOf(val));
        Formula inv_decl1 = (x28.always()).forAll(this_p1.oneOf(proc));
        Formula inv_decl2 = (inv.join(Expression.UNIV)).in(proc).always();

        Variable this_p2 = Variable.unary("this");
        Expression this_ouv = this_p2.join(ouv);
        Variable v1 = Variable.unary("v1");
        Formula x29 = (this_ouv.in(val).and(this_ouv.one())).forAll(v1.oneOf(val));
        Formula ouv_decl1 = (x29.always()).forAll(this_p2.oneOf(proc));
        Formula ouv_decl2 = (ouv.join(Expression.UNIV)).in(proc).always();

        Formula nin_decl2 = nin.in(proc).always();

        Formula init = nin.no();

        Variable p1 = Variable.unary("p1");
        Formula p1_nin = p1.in(nin);
        Expression p1_inv = p1.join(inv);
        Expression p1_ouv = p1.join(ouv);
        Formula pub = pub(p1_inv, p1_nin);
        Formula sec = sec(p1_ouv, p1_nin);
        Formula nop = nop(p1_inv, p1_ouv, p1_nin);
        Formula ops = pub.or(sec).or(nop).forAll(p1.oneOf(a.union(b)));

        Formula a_nin = a.in(nin);
        Expression a_inv = a.join(inv);
        Formula b_nin = b.in(nin);
        Expression b_inv = b.join(inv);
        Formula sync = pub(a_inv, a_nin).iff(pub(b_inv, b_nin));

        Variable p2 = Variable.unary("p2");
        Expression p2_inv = p2.join(inv);
        Formula p2_nin = p2.in(nin);
        Expression p2_ouv = p2.join(ouv);
        Formula fair = (pub(p2_inv, p2_nin).or(sec(p2_ouv, p2_nin))).eventually().forAll(p2.oneOf(proc));

        Formula trace = (ops.and(sync).and(fair)).always();

        Variable v_inv = Variable.unary_variable("v_inv");
        Variable v_ouv = Variable.unary_variable("v_ouv");
        Variable v_nin = Variable.unary_variable("v_nin");
        Formula c_pub = pub(v_inv, v_nin.some());
        Formula c_sec = sec(v_ouv, v_nin.some());
        Formula c_nop = nop(v_inv, v_ouv, v_nin.some());
        Formula c_ops = c_pub.or(c_sec).or(c_nop);
        Formula prop_ouv = a.join(ouv).eq(v_ouv);
        Formula prop_inv = b.join(inv).eq(v_inv);
        Formula c_init = v_nin.no();
        Formula c_prop = c_init.and(Formula.compose(FormulaOperator.AND, c_ops, prop_ouv, prop_inv).always());
        Formula check = c_prop.forSome(v_inv.oneOf(val).and(v_ouv.oneOf(val)).and(v_nin.setOf(a))).not();

        Formula formula = Formula.compose(FormulaOperator.AND, a_disj_b, inv_decl1, inv_decl2, ouv_decl1, ouv_decl2, nin_decl2, init, trace, check);

        ExtendedOptions opt = new ExtendedOptions();
        opt.setSolver(SATFactory.DEFAULT);
        opt.setBitwidth(1);
        opt.setSymmetryBreaking(20);
        opt.setSkolemDepth(1);
        opt.setAllowHOL(true);
        opt.setHolSome4AllMaxIter(50000);
        opt.setMinTraceLength(3);
        opt.setMaxTraceLength(7);
        opt.setRunTemporal(true);
        opt.setRunUnbounded(false);
        PardinusSolver solver = new PardinusSolver(opt);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(formula,bounds);
        System.out.println(sol.toString());
    }

    static Formula pub(Expression inv, Formula nin) {
        return nin.not().and(nin.after()).and(inv.prime().eq(inv));
    }

    static Formula sec(Expression ouv, Formula nin) {
        return nin.and(nin.not().after()).and(ouv.prime().eq(ouv));
    }

    static Formula nop(Expression inv, Expression ouv, Formula nin) {
        return nin.iff(nin.after()).and(ouv.eq(ouv.prime())).and(inv.eq(inv.prime()));
    }
}
