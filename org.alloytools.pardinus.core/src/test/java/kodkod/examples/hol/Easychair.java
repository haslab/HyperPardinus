package kodkod.examples.hol;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.ExtendedOptions;

/*
  ==================================================
    kodkod formula:
  ==================================================
    no (P1 & P2) and
    no (addAssignment & addReview) and
    no ((addAssignment + addReview) & updateReview) and
    (all GNI_this: P1 + P2 |
      (GNI_this . Process.oracle) in (Reviewer -> Article ->
      Decision) and
      (all v0: Reviewer |
        (v0 . (GNI_this . Process.oracle)) in (Article ->
        Decision) and
        (all v1: Article |
          one (v1 . (v0 . (GNI_this . Process.oracle))) and
          (v1 . (v0 . (GNI_this . Process.oracle))) in Decision) and
        (all v2: Decision |
          ((v0 . (GNI_this . Process.oracle)) . v2) in Article)) and
      (all v3: univ, v4: univ |
        ((v4 -> v3) in (Article -> Decision) and
         (all v5: Article |
           one (v5 . (v4 -> v3)) and
           (v5 . (v4 -> v3)) in Decision) and
         (all v6: Decision |
           ((v4 -> v3) . v6) in Article)) implies
        (((GNI_this . Process.oracle) . v3) . v4) in Reviewer)) and
    (((Process.oracle . univ) . univ) . univ) in (P1 + P2) and
    (all GNI_this: P1 + P2 |
      (GNI_this . Process.assigns) in (Reviewer -> Article) and
      (all v7: Reviewer |
        (v7 . (GNI_this . Process.assigns)) in Article) and
      (all v8: Article |
        some ((GNI_this . Process.assigns) . v8) and
        ((GNI_this . Process.assigns) . v8) in Reviewer)) and
    ((Process.assigns . univ) . univ) in (P1 + P2) and
    always (all GNI_this: P1 + P2 |
     (GNI_this . Process.reviews) in (Reviewer -> Article ->
     Decision)) and
    always ((((Process.reviews . univ) . univ) . univ) in (P1 +
    P2)) and
    (D/Ord . (D/Ord -> D/Ord.First)) in Decision and
    (D/Ord . (D/Ord -> D/Ord.Next)) in (Decision -> Decision) and
    ord[D/Ord.Next, Decision, D/Ord.First, Decision_last] and
    (ordering/Ord . ordering/Ord.First) in (addAssignment + addReview +
    updateReview) and
    (ordering/Ord . ordering/Ord.Next) in ((addAssignment + addReview +
    updateReview) -> (addAssignment + addReview +
    updateReview)) and
    (all v9: addAssignment + addReview + updateReview |
      (v9 = (ordering/Ord . ordering/Ord.First) or
       one ((ordering/Ord . ordering/Ord.Next) . v9)) and
      (v9 = ((addAssignment + addReview + updateReview) - ((
       ordering/Ord . ordering/Ord.Next) . (addAssignment + addReview +
       updateReview))) or
       one (v9 . (ordering/Ord . ordering/Ord.Next))) and
      !(v9 in (v9 . ^(ordering/Ord . ordering/Ord.Next)))) and
    (addAssignment + addReview + updateReview) in ((ordering/Ord .
    ordering/Ord.First) . *(ordering/Ord . ordering/Ord.Next)) and
    no ((ordering/Ord . ordering/Ord.Next) . (ordering/Ord . ordering/Ord.First)
    ) and
    !(all GNI_a: Reviewer |
       (no (P1 . Process.reviews) and
        always (some trace_a: Reviewer, trace_t: Article, trace_d:
        Decision |
         (trace_t in (trace_a . (P1 . Process.assigns)) and
          trace_d in (trace_t . (trace_a . (P1 . Process.oracle))) and
          (P1 . Process.reviews)' = ((P1 . Process.reviews) +
          (trace_a -> trace_t -> trace_d)) and
          !(trace_t in ((trace_a . (P1 . Process.reviews)) .
            Decision))) or
         (!(trace_t in ({decided_t: Article, decided_d: Decision |
            some ((P1 . Process.assigns) . decided_t) and
            (((P1 . Process.reviews) . decided_d) . decided_t) = ((
            P1 . Process.assigns) . decided_t)} . Decision)) and
          trace_t in ((trace_a . (P1 . Process.reviews)) .
          Decision) and
          (((P1 . Process.reviews) . Decision) . trace_t) = ((
          P1 . Process.assigns) . trace_t) and
          trace_d in ((trace_t . (Reviewer . (P1 .
          Process.reviews))) - ((trace_t . (Reviewer . (P1 .
          Process.reviews))) . ^D/Ord.Next)) and
          !(trace_d in (trace_t . (trace_a . (P1 . Process.reviews)))) and
          (P1 . Process.reviews)' = (((P1 . Process.reviews) -
          (trace_a -> trace_t -> Decision)) + (trace_a -> trace_t ->
          trace_d))) or
         (P1 . Process.reviews)' = (P1 . Process.reviews)) and
        eventually (({decided_t: Article, decided_d: Decision | some (
        (P1 . Process.assigns) . decided_t) and
        (((P1 . Process.reviews) . decided_d) . decided_t) = ((P1 .
        Process.assigns) . decided_t)} . Decision) = Article) and
        no (P2 . Process.reviews) and
        always (some trace_a: Reviewer, trace_t: Article, trace_d:
        Decision |
         (trace_t in (trace_a . (P2 . Process.assigns)) and
          trace_d in (trace_t . (trace_a . (P2 . Process.oracle))) and
          (P2 . Process.reviews)' = ((P2 . Process.reviews) +
          (trace_a -> trace_t -> trace_d)) and
          !(trace_t in ((trace_a . (P2 . Process.reviews)) .
            Decision))) or
         (!(trace_t in ({decided_t: Article, decided_d: Decision |
            some ((P2 . Process.assigns) . decided_t) and
            (((P2 . Process.reviews) . decided_d) . decided_t) = ((
            P2 . Process.assigns) . decided_t)} . Decision)) and
          trace_t in ((trace_a . (P2 . Process.reviews)) .
          Decision) and
          (((P2 . Process.reviews) . Decision) . trace_t) = ((
          P2 . Process.assigns) . trace_t) and
          trace_d in ((trace_t . (Reviewer . (P2 .
          Process.reviews))) - ((trace_t . (Reviewer . (P2 .
          Process.reviews))) . ^D/Ord.Next)) and
          !(trace_d in (trace_t . (trace_a . (P2 . Process.reviews)))) and
          (P2 . Process.reviews)' = (((P2 . Process.reviews) -
          (trace_a -> trace_t -> Decision)) + (trace_a -> trace_t ->
          trace_d))) or
         (P2 . Process.reviews)' = (P2 . Process.reviews)) and
        eventually (({decided_t: Article, decided_d: Decision | some (
        (P2 . Process.assigns) . decided_t) and
        (((P2 . Process.reviews) . decided_d) . decided_t) = ((P2 .
        Process.assigns) . decided_t)} . Decision) = Article) and
        always (({decided_t: Article, decided_d: Decision | some ((
        P1 . Process.assigns) . decided_t) and
        (((P1 . Process.reviews) . decided_d) . decided_t) = ((P1 .
        Process.assigns) . decided_t)} . Decision) = ({decided_t:
        Article, decided_d: Decision | some ((P2 .
        Process.assigns) . decided_t) and
        (((P2 . Process.reviews) . decided_d) . decided_t) = ((P2 .
        Process.assigns) . decided_t)} . Decision))) implies
       (some GNI_ot: set Reviewer -> Article -> Decision, GNI_at:
        set Reviewer -> Article, GNI_rt: set Reviewer ->
        Article -> Decision |
         GNI_ot in (Reviewer -> Article -> Decision) and
         (all v10: Reviewer |
           (v10 . GNI_ot) in (Article -> Decision) and
           (all v11: Article |
             one (v11 . (v10 . GNI_ot)) and
             (v11 . (v10 . GNI_ot)) in Decision) and
           (all v12: Decision |
             ((v10 . GNI_ot) . v12) in Article)) and
         (all v13: univ, v14: univ |
           ((v14 -> v13) in (Article -> Decision) and
            (all v15: Article |
              one (v15 . (v14 -> v13)) and
              (v15 . (v14 -> v13)) in Decision) and
            (all v16: Decision |
              ((v14 -> v13) . v16) in Article)) implies
           ((GNI_ot . v13) . v14) in Reviewer) and
         GNI_at in (Reviewer -> Article) and
         (all v17: Reviewer |
           (v17 . GNI_at) in Article) and
         (all v18: Article |
           some (GNI_at . v18) and
           (GNI_at . v18) in Reviewer) and
         GNI_rt in (Reviewer -> Article -> Decision) and
         no GNI_rt and
         always (some trace_a: Reviewer, trace_t: Article, trace_d:
         Decision |
          (trace_t in (trace_a . GNI_at) and
           trace_d in (trace_t . (trace_a . GNI_ot)) and
           (GNI_rt)' = (GNI_rt + (trace_a -> trace_t -> trace_d)) and
           !(trace_t in ((trace_a . GNI_rt) . Decision))) or
          (!(trace_t in ({decided_t: Article, decided_d: Decision |
             some (GNI_at . decided_t) and
             ((GNI_rt . decided_d) . decided_t) = (GNI_at . decided_t)} .
             Decision)) and
           trace_t in ((trace_a . GNI_rt) . Decision) and
           ((GNI_rt . Decision) . trace_t) = (GNI_at . trace_t) and
           trace_d in ((trace_t . (Reviewer . GNI_rt)) - ((trace_t . (
           Reviewer . GNI_rt)) . ^D/Ord.Next)) and
           !(trace_d in (trace_t . (trace_a . GNI_rt))) and
           (GNI_rt)' = ((GNI_rt - (trace_a -> trace_t -> Decision)) + (
           trace_a -> trace_t -> trace_d))) or
          (GNI_rt)' = GNI_rt) and
         eventually (({decided_t: Article, decided_d: Decision | some
         (GNI_at . decided_t) and
         ((GNI_rt . decided_d) . decided_t) = (GNI_at . decided_t)} .
         Decision) = Article) and
         GNI_ot in (Reviewer -> Article -> Decision) and
         (all v10: Reviewer |
           (v10 . GNI_ot) in (Article -> Decision) and
           (all v11: Article |
             one (v11 . (v10 . GNI_ot)) and
             (v11 . (v10 . GNI_ot)) in Decision) and
           (all v12: Decision |
             ((v10 . GNI_ot) . v12) in Article)) and
         (all v13: univ, v14: univ |
           ((v14 -> v13) in (Article -> Decision) and
            (all v15: Article |
              one (v15 . (v14 -> v13)) and
              (v15 . (v14 -> v13)) in Decision) and
            (all v16: Decision |
              ((v14 -> v13) . v16) in Article)) implies
           ((GNI_ot . v13) . v14) in Reviewer) and
         GNI_at in (Reviewer -> Article) and
         (all v17: Reviewer |
           (v17 . GNI_at) in Article) and
         (all v18: Article |
           some (GNI_at . v18) and
           (GNI_at . v18) in Reviewer) and
         GNI_rt in (Reviewer -> Article -> Decision) and
         always ((GNI_a . (P1 . Process.assigns)) = (GNI_a . GNI_at) and
         ((P1 . Process.oracle) & (Reviewer -> (GNI_a . (P1 .
         Process.assigns)) -> Decision)) = (GNI_ot & (Reviewer ->
         (GNI_a . GNI_at) -> Decision)) and
         (((GNI_a . (P1 . Process.assigns)) -> univ) & {decided_t:
         Article, decided_d: Decision | some ((P1 .
         Process.assigns) . decided_t) and
         (((P1 . Process.reviews) . decided_d) . decided_t) = ((
         P1 . Process.assigns) . decided_t)}) = (((GNI_a . GNI_at) ->
         univ) & {decided_t: Article, decided_d: Decision | some (
         GNI_at . decided_t) and
         ((GNI_rt . decided_d) . decided_t) = (GNI_at . decided_t)}) and
         ((P1 . Process.assigns) & (univ -> (GNI_a . (P1 .
         Process.assigns)))) = (GNI_at & (univ -> (GNI_a . GNI_at))) and
         (((Article - (GNI_a . ((P1 . Process.assigns) + (P2 .
         Process.assigns)))) -> univ) & {decided_t: Article, decided_d:
         Decision | some ((P2 . Process.assigns) . decided_t) and
         (((P2 . Process.reviews) . decided_d) . decided_t) = ((
         P2 . Process.assigns) . decided_t)}) = (((Article - (
         GNI_a . ((P1 . Process.assigns) + (P2 .
         Process.assigns)))) -> univ) & {decided_t: Article, decided_d:
         Decision | some (GNI_at . decided_t) and
         ((GNI_rt . decided_d) . decided_t) = (GNI_at . decided_t)})))) and
    Int/next = Int/next and
    seq/Int = seq/Int and
    String = String and
    Decision = Decision and
    Reviewer = Reviewer and
    Article = Article and
    P1 = P1 and
    P2 = P2 and
    addAssignment = addAssignment and
    addReview = addReview and
    updateReview = updateReview and
    D/Ord = D/Ord and
    ordering/Ord = ordering/Ord and
    ordering/Ord.First = ordering/Ord.First and
    ordering/Ord.Next = ordering/Ord.Next and
    Decision_last = Decision_last and
    Process.oracle = Process.oracle and
    Process.assigns = Process.assigns and
    Process.reviews = Process.reviews and
    D/Ord.First = D/Ord.First and
    D/Ord.Next = D/Ord.Next
  ==================================================
*/

// TODO:
//  - when not working
//  - duplicated typing of quants
//  - missing always on types
//  - hol vars not marked mutable
//  - with outermost quantification of reviewer rather than agent doesn't work

public final class Easychair {

    static Relation decision = Relation.unary("Decision");
    static Relation reviewer = Relation.unary("Reviewer");
    static Relation agent = Relation.unary("Agent");
    static Relation article = Relation.unary("Article");
    static Relation decision_last = Relation.unary("Decision_last");
    static Relation decision_first = Relation.unary("D/Ord.First");
    static Relation decision_next = Relation.nary("D/Ord.Next", 2);

    public static void main(String[] args) throws Exception {
        int n = 2, m = 3;

        Relation p1 = Relation.unary("P1");
        Relation p2 = Relation.unary("P2");
        Relation oracle = Relation.nary("Process.oracle", 4);
        Relation assigns = Relation.nary("Process.assigns", 3);
        Relation reviews = Relation.variable("Process.reviews", 4);

        List<String> atomlist = new ArrayList<>();
        atomlist.add("P1");
        atomlist.add("P2");

        for (int i = 0; i < m; i++) {
            atomlist.add("D"+i);
        }

        for (int i = 0; i < n; i++) {
            atomlist.add("R"+i);
            atomlist.add("A"+i);
        }

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        PardinusBounds bounds = new PardinusBounds(universe);

        TupleSet x3_upper = factory.noneOf(1);
        for (int i = 0; i < m; i++)
            x3_upper.add(factory.tuple("D"+i));
        bounds.boundExactly(decision, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        for (int i = 0; i < n; i++)
            x4_upper.add(factory.tuple("R"+i));
        bounds.bound(reviewer, x4_upper);

        TupleSet x41_upper = factory.noneOf(1);
        x41_upper.add(factory.tuple("R0"));
        bounds.bound(agent, x41_upper);


        TupleSet x5_upper = factory.noneOf(1);
        for (int i = 0; i < n; i++)
            x5_upper.add(factory.tuple("A"+i));
        bounds.bound(article, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("P1"));
        bounds.boundExactly(p1, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("P2"));
        bounds.boundExactly(p2, x7_upper);

        TupleSet x15_upper = factory.noneOf(1);
        for (int i = 0; i < m; i++)
            x15_upper.add(factory.tuple("D"+i));
        bounds.bound(decision_last, x15_upper);

        TupleSet x16_upper = factory.noneOf(4);
        for (int i = 0; i < m; i++)
            for (int j = 0; j < n; j++)
                for (int k = 0; k < n; k++) {
                    x16_upper.add(factory.tuple("P1").product(factory.tuple("R" + j)).product(factory.tuple("A" + k)).product(factory.tuple("D" + i)));
                    x16_upper.add(factory.tuple("P2").product(factory.tuple("R" + j)).product(factory.tuple("A" + k)).product(factory.tuple("D" + i)));
                }

        bounds.bound(oracle, x16_upper);

        TupleSet x17_upper = factory.noneOf(3);
        for (int j = 0; j < n; j++)
            for (int k = 0; k < n; k++) {
                x17_upper.add(factory.tuple("P1").product(factory.tuple("R"+j)).product(factory.tuple("A"+k)));
                x17_upper.add(factory.tuple("P2").product(factory.tuple("R"+j)).product(factory.tuple("A"+k)));
            }
        bounds.bound(assigns, x17_upper);

        bounds.bound(reviews, x16_upper);

        TupleSet x13_upper = factory.noneOf(1);
        x13_upper.add(factory.tuple("D0"));
        bounds.boundExactly(decision_first, x13_upper);

        TupleSet x14_upper = factory.noneOf(1);
        x14_upper.add(factory.tuple("D"+(m-1)));
        bounds.boundExactly(decision_last, x14_upper);

        TupleSet x20_upper = factory.noneOf(2);
        for (int i = 0; i < m-1; i++)
            x20_upper.add(factory.tuple("D"+i).product(factory.tuple("D"+(i+1))));
        bounds.boundExactly(decision_next, x20_upper);

        Formula disj_p= p1.intersection(p2).no();
        Expression p=p1.union(p2);

        Variable po=Variable.unary("p");
        Expression vo = po.join(oracle);
        Variable x41=Variable.unary("v0");
        Formula type_oracle1 = vo.in(reviewer.product(article.product(decision)));
        Variable x49=Variable.unary("v1");
        Variable x56=Variable.unary("v2");
        Formula type_oracle2 = x41.join(vo).in(article.product(decision)).and(x49.join(x41.join(vo)).one().and(x49.join(x41.join(vo)).in(decision)).forAll(x49.oneOf(article))).and(x41.join(vo).join(x56).in(article).forAll(x56.oneOf(decision))).forAll(x41.oneOf(reviewer));
        Variable x62=Variable.unary("v3");
        Variable x65=Variable.unary("v4");
        Variable x74=Variable.unary("v5");
        Variable x81=Variable.unary("v6");
        Formula type_oracle3 = x65.product(x62).in(article.product(decision)).and(x74.join(x65.product(x62)).one().and(x74.join(x65.product(x62)).in(decision)).forAll(x74.oneOf(article))).and(x65.product(x62).join(x81).in(article).forAll(x81.oneOf(decision))).implies(vo.join(x62).join(x65).in(reviewer)).forAll(x62.oneOf(Expression.UNIV).and(x65.oneOf(Expression.UNIV)));
        Formula type_oracle4 = type_oracle1.and(type_oracle2).and(type_oracle3).forAll(po.oneOf(p));

        Formula type_oracle5= oracle.join(Expression.UNIV).join(Expression.UNIV).join(Expression.UNIV).in(p);

        Variable pa=Variable.unary("p");
        Expression va = pa.join(assigns);
        Variable x101=Variable.unary("v7");
        Variable x106=Variable.unary("v8");
        Formula type_assigns_1= va.in(reviewer.product(article)).and(x101.join(va).in(article).forAll(x101.oneOf(reviewer))).and(va.join(x106).some().and(va.join(x106).in(reviewer)).forAll(x106.oneOf(article))).forAll(pa.oneOf(p));
        Formula type_assigns_2= assigns.join(Expression.UNIV).join(Expression.UNIV).in(p);

        Variable pr=Variable.unary("p");
        Expression vr = pr.join(reviews);
        Formula type_reviews1= vr.in(reviewer.product(article.product(decision))).forAll(pr.oneOf(p)).always();
        Formula type_reviews2= reviews.join(Expression.UNIV).join(Expression.UNIV).join(Expression.UNIV).in(p).always();

        Expression p1_assigns = p1.join(assigns);
        Expression p1_oracle = p1.join(oracle);
        Expression p1_reviews = p1.join(reviews);
        Expression p2_assigns = p2.join(assigns);
        Expression p2_oracle = p2.join(oracle);
        Expression p2_reviews = p2.join(reviews);
        Formula sync = getDecidedExpression(p1_reviews, p1_assigns).join(decision).eq(getDecidedExpression(p2_reviews, p2_assigns).join(decision)).always();
        Formula traces = getTraceFormula(p1_reviews, p1_assigns, p1_oracle).and(getTraceFormula(p2_reviews, p2_assigns, p2_oracle)).and(sync);

        Variable p3_oracle=Variable.nary("GNI_ot",3);
        Variable p3_assigns=Variable.nary("GNI_at",2);
        Variable p3_reviews=Variable.variable("GNI_rt",3);

        Formula type_rt = p3_reviews.in(reviewer.product(article.product(decision))).always();
        Variable x480=Variable.unary("v17");
        Variable x485=Variable.unary("v18");
        Formula type_at = p3_assigns.in(reviewer.product(article)).and(x480.join(p3_assigns).in(article).forAll(x480.oneOf(reviewer))).and(p3_assigns.join(x485).some().and(p3_assigns.join(x485).in(reviewer)).forAll(x485.oneOf(article)));
        Variable x429=Variable.unary("v10");
        Variable x437=Variable.unary("v11");
        Variable x444=Variable.unary("v12");
        Variable x450=Variable.unary("v13");
        Variable x452=Variable.unary("v14");
        Variable x461=Variable.unary("v15");
        Variable x468=Variable.unary("v16");
        Formula type_ot = p3_oracle.in(reviewer.product(article.product(decision))).and(x429.join(p3_oracle).in(article.product(decision)).and(x437.join(x429.join(p3_oracle)).one().and(x437.join(x429.join(p3_oracle)).in(decision)).forAll(x437.oneOf(article))).and(x429.join(p3_oracle).join(x444).in(article).forAll(x444.oneOf(decision))).forAll(x429.oneOf(reviewer))).and(x452.product(x450).in(article.product(decision)).and(x461.join(x452.product(x450)).one().and(x461.join(x452.product(x450)).in(decision)).forAll(x461.oneOf(article))).and(x452.product(x450).join(x468).in(article).forAll(x468.oneOf(decision))).implies(p3_oracle.join(x450).join(x452).in(reviewer)).forAll(x450.oneOf(Expression.UNIV).and(x452.oneOf(Expression.UNIV))));
        Formula type_hol = Formula.compose(FormulaOperator.AND, type_ot, type_at, type_rt);
        Formula same_high = article.difference(agent.join((p1_assigns.union(p2_assigns)))).product(Expression.UNIV).intersection(getDecidedExpression(p2_reviews, p2_assigns)).eq(article.difference(agent.join(p1_assigns.union(p2_assigns))).product(Expression.UNIV).intersection(getDecidedExpression(p3_reviews,p3_assigns)));
        Formula same_low = agent.join(p1_assigns).eq(agent.join(p3_assigns)).and(p1_oracle.intersection(reviewer.product(agent.join(p1_assigns).product(decision))).eq(p3_oracle.intersection(reviewer.product(agent.join(p3_assigns).product(decision)))).and(agent.join(p1_assigns).product(Expression.UNIV).intersection(getDecidedExpression(p1_reviews, p1_assigns)).eq(agent.join(p3_assigns).product(Expression.UNIV).intersection(getDecidedExpression(p3_reviews,p3_assigns))))).and(p1_assigns.intersection(Expression.UNIV.product(agent.join(p1_assigns))).eq(p3_assigns.intersection(Expression.UNIV.product(agent.join(p3_assigns)))));
        Formula body = (same_low.and(same_high)).always();
        Formula gni = body.forSome(p3_oracle.setOf(reviewer.product(article.product(decision))).and(p3_assigns.setOf(reviewer.product(article))).and(p3_reviews.setOf(reviewer.product(article.product(decision)))),type_hol.and(getTraceFormula(p3_reviews, p3_assigns, p3_oracle)));
        Formula check= traces.implies(gni);

        Expression agt = agent, otr = reviewer.difference(agent), own1 = agent.join(p1_assigns), cnf1 = article.difference(agent.join(p1_assigns));
        Formula run1 = agt.join(p1_assigns).one();
        Formula run2 = otr.join(p1_assigns).eq(article);
        Formula run22 = otr.join(p2_assigns).eq(article);
        Formula run3 = getTraceFormula(p1_reviews, p1_assigns, p1_oracle).and(getTraceFormula(p2_reviews, p2_assigns, p2_oracle)).and((getDecidedExpression(p1_reviews, p1_assigns).join(decision).eq(getDecidedExpression(p2_reviews, p2_assigns).join(decision))).always());
        Formula run4 = p1_oracle.eq(agent.product(article).product(decision_last).union((reviewer.difference(agent)).product(agent.join(p1_assigns)).product(decision_first.join(decision_next))).union((reviewer.difference(agent)).product(article.difference(agent.join(p1_assigns))).product(decision_first)));
        Formula run5 = p2_oracle.eq(agent.product(article).product(decision_last).union((reviewer.difference(agent)).product(agent.join(p1_assigns)).product(decision_first.join(decision_next))).union((reviewer.difference(agent)).product(article.difference(agent.join(p1_assigns))).product(decision_last)));
        Formula run6 = agent.join(p1_assigns).product(decision_first).in(getDecidedExpression(p1_reviews,p1_assigns)).eventually();
        Formula run7 = (article.difference(agent.join(p1_assigns))).product(decision_first).in(getDecidedExpression(p1_reviews,p1_assigns)).eventually();
        Formula run8 = agent.join(p2_assigns).product(decision_first.join(decision_next)).in(getDecidedExpression(p2_reviews,p2_assigns)).eventually();
        Formula run9 = (article.difference(agent.join(p2_assigns))).product(decision_last).in(getDecidedExpression(p2_reviews,p2_assigns)).eventually();

        Formula run = Formula.compose(FormulaOperator.AND, run1, run2, run3, run4, run5, run6, run7, run8, run9);
        Formula f=Formula.compose(FormulaOperator.AND, run2, run22, disj_p, type_oracle4, type_oracle5, type_assigns_1, type_assigns_2, type_reviews1, type_reviews2, check.not());

        ExtendedOptions opt = new ExtendedOptions();
        opt.setSolver(SATFactory.DEFAULT);
        opt.setBitwidth(1);
        opt.setSymmetryBreaking(20);
        opt.setSkolemDepth(1);
        opt.setAllowHOL(true);
        opt.setHolSome4AllMaxIter(50000);
        opt.setMinTraceLength(1);
        opt.setMaxTraceLength(10);
        opt.setRunTemporal(true);
        opt.setRunUnbounded(false);
        PardinusSolver solver = new PardinusSolver(opt);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(f,bounds);
        System.out.println(sol.toString());
    }

    private static Formula getTraceFormula(Expression rt, Expression at, Expression ot) {
        Variable a = Variable.unary("trace_a");
        Variable t = Variable.unary("trace_t");
        Variable d = Variable.unary("trace_d");
        Formula init = rt.no();
        Formula fairness = getDecidedExpression(rt, at).join(decision).eq(article).eventually();
        Formula add = t.in(a.join(at)).and(d.in(t.join(a.join(ot))).and(rt.prime().eq(rt.union(a.product(t.product(d)))))).and(t.in(a.join(rt).join(decision)).not());
        Formula upd0 = t.in(getDecidedExpression(rt, at).join(decision)).not();
        Formula upd1 = t.in(a.join(rt).join(decision));
        Formula upd2 = d.in(t.join(a.join(rt))).not();
        Formula upd4 = rt.join(decision).join(t).eq(at.join(t));
        boolean bug = true;
        Expression x = bug?a.eq(agent).thenElse(article,t):t;
        Formula upd5 = d.in(x.join(reviewer.join(rt)));//.difference(x.join(reviewer.join(rt)).join(decision_next.closure())));
        Formula upd3 = rt.prime().eq(rt.difference(a.product(t.product(decision))).union(a.product(t.product(d))));
        Formula upd = Formula.compose(FormulaOperator.AND, upd0, upd1, upd2, upd3, upd4, upd5);
        Formula stutter = rt.prime().eq(rt);
        Formula events = add.or(upd).or(stutter).forSome(a.oneOf(reviewer).and(t.oneOf(article)).and(d.oneOf(decision))).always();
        return init.and(events).and(fairness);
    }

    private static Expression getDecidedExpression(Expression rt, Expression at) {
        Variable x218 = Variable.unary("decided_t");
        Variable x220 = Variable.unary("decided_d");
        return at.join(x218).some().and(rt.join(x220).join(x218).eq(at.join(x218))).comprehension(x218.oneOf(article).and(x220.oneOf(decision)));
    }
}
