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
import kodkod.engine.Solution;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.instance.Bounds;
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

public class HOL {

    static Relation val   = Relation.unary("Val");
    static Relation time  = Relation.unary("Time");
    static Relation a     = Relation.unary("A");
    static Relation b     = Relation.unary("B");
    static Relation loop  = Relation.unary("Loop");
    static Relation inv   = Relation.nary("Proc.inv", 3);
    static Relation ouv   = Relation.nary("Proc.ouv", 3);
    static Relation nin   = Relation.nary("Proc.nin", 2);
    static Relation first = Relation.unary("Ord.First");
    static Relation next  = Relation.nary("Ord.Next", 2);
    static Relation last  = Relation.unary("Ord.Last");

    public static void main(String args[]) {

        int nv = 3, nt = 6;

        List<String> atomlist = new ArrayList<String>(Arrays.asList("A$0", "B$0", "t/Ord$0"));
        for (int i = 0; i < nt; i++) {
            atomlist.add("Time$"+i);
        }
        for (int i = 0; i < nv; i++) {
            atomlist.add("Val$"+i);
        }

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        PardinusBounds bounds = new PardinusBounds(universe);

        TupleSet vals_bound = factory.range(factory.tuple("Val$0"), factory.tuple("Val$"+(nv-1)));
        TupleSet time_bound = factory.range(factory.tuple("Time$0"), factory.tuple("Time$"+(nt-1)));

        bounds.bound(val, vals_bound);
        bounds.boundExactly(time, time_bound);

        TupleSet x8_upper = factory.setOf(factory.tuple("A$0"));
        bounds.boundExactly(a, x8_upper);

        TupleSet x9_upper = factory.setOf(factory.tuple("B$0"));
        bounds.boundExactly(b, x9_upper);

        bounds.bound(loop, time_bound);

        TupleSet x12_upper = factory.noneOf(3);
        x12_upper.addAll(x8_upper.product(vals_bound).product(time_bound));
        x12_upper.addAll(x9_upper.product(vals_bound).product(time_bound));
        bounds.bound(inv, x12_upper);
        bounds.bound(ouv, x12_upper);

        TupleSet x14_upper = factory.noneOf(2);
        x14_upper.addAll(x8_upper.product(time_bound));
        x14_upper.addAll(x9_upper.product(time_bound));
        bounds.bound(nin, x14_upper);

        bounds.bound(first, time_bound);
        bounds.bound(last, time_bound);
        bounds.bound(next, time_bound.product(time_bound));

        Formula a_disj_b = a.intersection(b).no();
        Formula loop_decl = loop.in(time);
        Formula loop_mult = loop.one();

        Expression proc = a.union(b);

        Variable this_p1 = Variable.unary("this");
        Expression this_inv = this_p1.join(inv);
        Variable v0 = Variable.unary("v0");
        Expression v0_inv = v0.join(this_inv);
        Formula x28 = (this_inv.in(val.product(time))).and((v0_inv.in(time)).forAll(v0.oneOf(val)));
        Variable v1 = Variable.unary("v1");
        Expression inv_v1 = this_inv.join(v1);
        Formula x40 = (inv_v1.one()).and(inv_v1.in(val));
        Formula inv_decl1 = (x28.and(x40.forAll(v1.oneOf(time)))).forAll(this_p1.oneOf(proc));
        Formula inv_decl2 = (inv.join(Expression.UNIV)).join(Expression.UNIV).in(proc);

        Variable this_p2 = Variable.unary("this");
        Expression this_ouv = this_p2.join(ouv);
        Variable v2 = Variable.unary("v2");
        Expression v2_this = v2.join(this_ouv);
        Formula x52 = (this_ouv.in(val.product(time))).and((v2_this.in(time)).forAll(v2.oneOf(val)));
        Variable v3 = Variable.unary("v3");
        Expression ouv_v3 = this_ouv.join(v3);
        Formula x64 = (ouv_v3.one()).and(ouv_v3.in(val));
        Formula ouv_decl1 = (x52.and(x64.forAll(v3.oneOf(time)))).forAll(this_p2.oneOf(proc));
        Formula ouv_decl2 = ((ouv.join(Expression.UNIV)).join(Expression.UNIV)).in(proc);

        Variable this_p3 = Variable.unary("this");
        Expression this_nin = this_p3.join(nin);
        Formula nin_decl1 = (this_nin.in(time)).forAll(this_p3.oneOf(proc));

        Formula nin_decl2 = (nin.join(Expression.UNIV)).in(proc);

        Formula time_ord = next.totalOrder(time, first, last);

        Formula init = nin.join(first).no();

        Variable t = Variable.unary("t");
        Variable p1 = Variable.unary("p1");
        Expression p1_nin = p1.join(nin);
        Expression p1_inv = p1.join(inv);
        Expression p1_ouv = p1.join(ouv);
        Formula pub = pub(p1_inv, p1_nin, t);
        Formula sec = sec(p1_ouv, p1_nin, t);
        Formula nop = nop(p1_inv, p1_ouv, p1_nin, t);
        Formula ops = pub.or(sec).or(nop).forAll(p1.oneOf(a.union(b)));

        Expression a_nin = a.join(nin);
        Expression a_inv = a.join(inv);
        Expression b_nin = b.join(nin);
        Expression b_inv = b.join(inv);
        Formula sync = pub(a_inv, a_nin, t).iff(pub(b_inv, b_nin, t));

        Variable p2 = Variable.unary("p2");
        Variable t1 = Variable.unary("t1");
        Expression p2_inv = p2.join(inv);
        Expression p2_nin = p2.join(nin);
        Expression p2_ouv = p2.join(ouv);
        Formula fair = pub(p2_inv, p2_nin, t1).or(sec(p2_ouv, p2_nin, t1)).forSome(t1.oneOf(t.join((nxt()).closure().union(Expression.IDEN.intersection(time.product(Expression.UNIV)))))).forAll(p2.oneOf(proc));

        Formula trace = ops.and(sync).and(fair).forAll(t.oneOf(time));

        Variable v_inv = Variable.nary("v_inv", 2);
        Variable v_ouv = Variable.nary("v_ouv", 2);
        Variable v_nin = Variable.unary("v_nin");
        Variable c_t = Variable.unary("t");
        Formula c_mult = (v_inv.join(c_t).one().and(v_ouv.join(c_t).one()));
        Formula c_pub = pub(v_inv, v_nin, c_t);
        Formula c_sec = sec(v_ouv, v_nin, c_t);
        Formula c_nop = nop(v_inv, v_ouv, v_nin, c_t);
        Formula c_ops = c_pub.or(c_sec).or(c_nop);
        Formula prop_ouv = a.join(ouv).join(c_t).eq(v_ouv.join(c_t));
        Formula prop_inv = b.join(inv).join(c_t).eq(v_inv.join(c_t));
        Formula c_init = first.in(v_nin).not();
        Formula c_prop = c_init.and(Formula.compose(FormulaOperator.AND, c_mult, c_ops, prop_ouv, prop_inv).forAll(c_t.oneOf(time)));
        Formula check = c_prop.forSome(v_inv.setOf(val.product(time)).and(v_ouv.setOf(val.product(time))).and(v_nin.setOf(time))).not();

        Formula formula = Formula.compose(FormulaOperator.AND, a_disj_b, loop_decl, loop_mult, inv_decl1, inv_decl2, ouv_decl1, ouv_decl2, nin_decl1, nin_decl2, time_ord, init, trace, check);

        ExtendedOptions opt = new ExtendedOptions();
        opt.setReporter(new ConsoleReporter());
        opt.setAllowHOL(true);
        opt.setHolFullIncrements(false);
        opt.setHolSome4AllMaxIter(5000);
        HOLSolver slv = HOLSolver.solver(opt);
        Solution sol = slv.solve(formula, bounds);
        System.out.println(sol.toString());
    }

    static Expression nxt() {
        return next.union(last.product(loop));
    }

    static Formula pub(Expression inv, Expression nin, Expression t) {
        return t.in(nin).not().and(t.join(nxt()).in(nin)).and(inv.join(t.join(nxt())).eq(inv.join(t)));
    }

    static Formula sec(Expression ouv, Expression nin, Expression t) {
        return t.in(nin).and(t.join(nxt()).in(nin).not()).and(ouv.join(t.join(nxt())).eq(ouv.join(t)));
    }

    static Formula nop(Expression inv, Expression ouv, Expression nin, Expression t) {
        return t.in(nin).iff(t.join(nxt()).in(nin)).and(ouv.join(t.join(nxt())).eq(ouv.join(t))).and(inv.join(t.join(nxt())).eq(inv.join(t)));
    }
}
