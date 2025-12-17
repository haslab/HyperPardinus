package edu.mit.csail.sdg.translator;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprQt.Op;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.VisitQuery;
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;

public class TraceModels {

    final private Map<ExprHasName,TranslateAlloyToKodkod> trans         = new LinkedHashMap<ExprHasName,TranslateAlloyToKodkod>();
    final private TranslateAlloyToKodkod                  spec;
    final private StringBuilder                           mc_quants     = new StringBuilder();
    final private Map<ExprHasName,Character>              ids           = new HashMap<ExprHasName,Character>();
    final public Map<Expr,Expr>                           state_var2sig = new HashMap<Expr,Expr>();

    public TraceModels(A4Reporter rep, Iterable<Sig> sigs, Command cmd, A4Options opt) throws Err, IOException, InterruptedException {
        TranslateAlloyToKodkod tr = new TranslateAlloyToKodkod(rep, opt, sigs, cmd, false);

        opt.skolemDepth = 3;
        opt.unrolls = 3;
        opt.recordKodkod = true;
        opt.inferPartialInstance = false;

        TraceFormulas tdf = new TraceFormulas(opt.noSelfCompose);
        Expr trace_formula = cmd.formula.accept(new FlattenFormula()).accept(tdf);

        Map<ExprHasName,List<Expr>> state_var_formulas = tdf.extracts;
        for (ExprHasName e : state_var_formulas.keySet())
            state_var_formulas.get(e).addAll(state_var_formulas.getOrDefault(null, Collections.EMPTY_LIST));

        for (ExprHasName state_var : tdf.vars) {
            PrimSig state_sig = state_var.type().fold().get(0).get(0);
            cmd = cmd.change(state_sig, true, 1);
            state_var2sig.put(state_var, state_sig);
        }

        Map<ExprHasName,String> state_var2smv = new HashMap<ExprHasName,String>();
        Replacer replacer = new Replacer(state_var2sig, mc_quants);

        for (ExprHasName state_var : tdf.vars) {
            List<Sig> no_trace_sigs = new ArrayList<Sig>();
            no_trace_sigs.add((Sig) state_var2sig.get(state_var));
            sigs.forEach(sig -> {
                if (sig.isTrace == null)
                    no_trace_sigs.add(sig);
            });

            List<Expr> state_formulas_var = state_var_formulas.get(state_var);
            state_formulas_var.add(ExprConstant.TRUE.eventually()); // needed in case electrod moves everything to TS
            Expr state_formula_sig = ExprList.make(null, null, ExprList.Op.AND, state_formulas_var).accept(replacer);

            A4Options opt_clone = opt.dup();
            if (!trans.isEmpty())
                opt_clone.symmetry = 0;

            tr = new TranslateAlloyToKodkod(rep, opt_clone, no_trace_sigs, cmd, false);
            tr.makeFacts(state_formula_sig, false);
            trans.put(state_var, tr);
        }

        List<Sig> sigs_state_sigs = new ArrayList<Sig>();
        sigs.forEach(sig -> {
            if (sig.isTrace == null)
                sigs_state_sigs.add(sig);
        });
        char cnt = 'A';
        for (ExprHasName state_var : tdf.vars) {
            PrimSig s = new PrimSig(null, "_" + cnt + "###", null, (PrimSig) state_var2sig.get(state_var), Attr.ONE);
            sigs_state_sigs.add(s);
            if (!sigs_state_sigs.contains(s.parent))
                sigs_state_sigs.add(s.parent);
            state_var2sig.put(state_var, s);
            ids.put(state_var, cnt++);
        }
        opt.skolemDepth = -1;
        opt.symmetry = 0;
        tr = new TranslateAlloyToKodkod(rep, opt, sigs_state_sigs, cmd, true);


        Expr new_spec = trace_formula.accept(replacer);
        tr.makeFacts(new_spec, true);
        spec = tr;

    }

    TranslateAlloyToKodkod getModel(ExprHasName state_var) {
        return trans.get(state_var);
    }

    Character getId(ExprHasName state_var) {
        return ids.get(state_var);
    }

    public List<ExprHasName> getStateVars() {
        return new ArrayList(trans.keySet());
    }

    TranslateAlloyToKodkod getSpec() {
        return spec;
    }

    String quants() {
        return mc_quants.toString();
    }

    class Replacer extends VisitReturn<Expr> {

        private Map<Expr,Expr> state_var2sig;
        private StringBuilder  mc_quants;

        public Replacer(Map<Expr,Expr> state_var2sig, StringBuilder mc_quants) {
            this.state_var2sig = state_var2sig;
            this.mc_quants = mc_quants;
        }

        @Override
        public Expr visit(Macro macro) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(Assert x) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(Func x) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(Field x) throws Err {
            return x;
        }

        @Override
        public Expr visit(Sig x) throws Err {
            if (state_var2sig.containsKey(x))
                return state_var2sig.get(x);
            return x;
        }

        @Override
        public Expr visit(ExprVar x) throws Err {
            if (state_var2sig.containsKey(x))
                return state_var2sig.get(x);
            return x;
        }

        @Override
        public Expr visit(ExprUnary x) throws Err {
            Expr s = x.sub.accept(this);
            return x.op.make(x.pos, s);
        }

        @Override
        public Expr visit(ExprQt x) throws Err {
            List<Decl> decls = new ArrayList<Decl>();
            boolean hol = false;
            for (Decl d : x.decls) {
                Sig type = d.expr.type().fold().get(0).get(0);
                if (type.isTrace == null) {
                    Expr dexpr = d.expr.accept(this);
                    decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.isVar, d.names, dexpr));
                } else {
                    for (ExprHasName v : d.names)
                        mc_quants.append((x.op == Op.ALL ? "exists" : "forall") + " " + state_var2sig.get(v).toString().charAt(1) + ". ");
                    hol = true;
                }
            }

            Expr s = x.sub.accept(this);
            // hyperqb does not like formulas outside temporal operators
            if (hol && s instanceof ExprList) {
                List<Expr> args = new ArrayList<Expr>();
                for (Expr e : ((ExprList) s).args) {
                    boolean is_uny_temp = e instanceof ExprUnary && List.of(ExprUnary.Op.AFTER, ExprUnary.Op.BEFORE, ExprUnary.Op.ALWAYS, ExprUnary.Op.HISTORICALLY, ExprUnary.Op.EVENTUALLY, ExprUnary.Op.ONCE).contains(((ExprUnary) e).op);
                    boolean is_bin_temp = e instanceof ExprBinary && List.of(ExprBinary.Op.UNTIL, ExprBinary.Op.SINCE, ExprBinary.Op.RELEASES, ExprBinary.Op.TRIGGERED).contains(((ExprBinary) e).op);
                    if (!is_uny_temp && !is_bin_temp) {
                        Set<Expr> var_elems = new HashSet<>();

                        final VisitQuery<Object> q = new VisitQuery<Object>() {

                            @Override
                            public final Object visit(Sig x) {
                                if (x.isVariable != null)
                                    var_elems.add(x);
                                return null;
                            }

                            @Override
                            public final Object visit(Field x) {
                                if (x.isVariable != null)
                                    var_elems.add(x);
                                return null;
                            }

                        };
                        e.accept(q);
                        if (var_elems.isEmpty())
                            args.add(e.always());
                        else
                            args.add(e);
                    } else
                        args.add(e);
                }
                s = ExprList.make(s.pos, s.closingBracket, ((ExprList) s).op, args);
            }
            if (decls.isEmpty())
                return s;
            else
                return x.op.make(x.pos, x.closingBracket, decls, s);
        }

        @Override
        public Expr visit(ExprLet x) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(ExprITE x) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(ExprConstant x) throws Err {
            return x;
        }

        @Override
        public Expr visit(ExprCall x) throws Err {
            throw new RuntimeException();
        }

        @Override
        public Expr visit(ExprList x) throws Err {
            List<Expr> args = new ArrayList<Expr>();
            for (Expr s : x.args)
                args.add(s.accept(this));
            return ExprList.make(x.pos, x.closingBracket, x.op, args);
        }

        @Override
        public Expr visit(ExprBinary x) throws Err {
            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            return x.op.make(x.pos, x.closingBracket, l, r);
        }
    }


}
