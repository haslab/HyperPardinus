package edu.mit.csail.sdg.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Attr;
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


public class TraceFormulas extends VisitReturn<Expr> {

    Set<ExprHasName>                         acts            = new HashSet<>();
    List<ExprHasName>                        vars            = new ArrayList<>();
    boolean                                  univ;
    public final Map<ExprHasName,List<Expr>> extracts        = new HashMap<ExprHasName,List<Expr>>();

    VisitReturn<Set<ExprHasName>>            getVars         = new VisitReturn<Set<ExprHasName>>() {

                                                                 @Override
                                                                 public final Set<ExprHasName> visit(ExprVar x) throws Err {
                                                                     Set<ExprHasName> res = new HashSet<ExprHasName>();
                                                                     Sig tp = x.type().fold().get(0).get(0);
                                                                     if (tp.isTrace != null)
                                                                         res.add(x);
                                                                     return res;
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprBinary x) throws Err {
                                                                     Set<ExprHasName> res = x.left.accept(this);
                                                                     res.addAll(x.right.accept(this));
                                                                     return res;
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprList x) throws Err {
                                                                     Set<ExprHasName> res = new HashSet<ExprHasName>();
                                                                     for (Expr c : x.args)
                                                                         res.addAll(c.accept(this));
                                                                     return res;
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprCall x) throws Err {
                                                                     throw new RuntimeException();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprConstant x) throws Err {
                                                                     return new HashSet<ExprHasName>();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprITE x) throws Err {
                                                                     Set<ExprHasName> res = x.left.accept(this);
                                                                     res.addAll(x.right.accept(this));
                                                                     res.addAll(x.cond.accept(this));
                                                                     return res;
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprLet x) throws Err {
                                                                     throw new RuntimeException();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprQt x) throws Err {
                                                                     Set<ExprHasName> res = x.sub.accept(this);
                                                                     for (Decl d : x.decls)
                                                                         res.addAll(d.expr.accept(this));
                                                                     return res;
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(ExprUnary x) throws Err {
                                                                     return x.sub.accept(this);
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(Sig x) throws Err {
                                                                     return new HashSet<ExprHasName>();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(Field x) throws Err {
                                                                     return new HashSet<ExprHasName>();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(Func x) throws Err {
                                                                     throw new RuntimeException();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(Assert x) throws Err {
                                                                     throw new RuntimeException();
                                                                 }

                                                                 @Override
                                                                 public Set<ExprHasName> visit(Macro macro) throws Err {
                                                                     throw new RuntimeException();
                                                                 }
                                                             };


    private Expr                             current_new_var = null;
    private boolean                          noSelfCompose;

    public TraceFormulas(boolean noSelfCompose) {
        this.noSelfCompose = noSelfCompose;
    }

    @Override
    public Expr visit(ExprBinary x) throws Err {
        if (x.op == ExprBinary.Op.JOIN) {
            if (newvars.containsKey(x.left))
                if (current_new_var == null) {
                    current_new_var = x.left;
                } else {
                    throw new RuntimeException("Cannot disambiguate context for self-composition: " + x);
                }

        }

        if (!((x.op == ExprBinary.Op.AND && !univ) || (x.op == ExprBinary.Op.OR && univ)))

        {
            boolean tl = toplevel;
            toplevel = false;
            Set<ExprHasName> tmp = acts;
            acts = new HashSet<ExprHasName>();

            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            current_new_var = null;

            Expr res = x.op.make(x.pos, x.closingBracket, l, r);
            acts = tmp;
            toplevel = tl;
            return addSelf(res);
        } else {
            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            current_new_var = null;

            x = (ExprBinary) x.op.make(x.pos, x.closingBracket, l, r);
            return x;
        }

    }

    private Expr addSelf(Expr xx) {
        if (!toplevel)
            return xx;
        Expr x = xx;
        Set<ExprHasName> vars = xx.accept(getVars);
        for (ExprHasName v : acts)
            if ((vars.contains(v) && vars.size() == 1)) {
                List<Expr> lst = extracts.get(v);
                if (univ)
                    x = xx.not().accept(new FlattenFormula());
                if (isFSM(x)) {
                    lst.add(x);
                    return univ ? ExprConstant.FALSE : ExprConstant.TRUE;
                } else {

                    return xx;
                }
            }
        if (vars.size() == 0) {
            List<Expr> lst = extracts.computeIfAbsent(null, e -> new ArrayList<Expr>());
            if (univ)
                x = xx.not().accept(new FlattenFormula());
            if (isFSM(x)) {
                lst.add(x);
                return univ ? ExprConstant.FALSE : ExprConstant.TRUE;
            } else {
                return xx;
            }
        }
        return xx;

    }

    private boolean isFSM(Expr x) {
        return x.accept(new VisitQuery<Boolean>() {

            @Override
            public Boolean visit(ExprBinary x) throws Err {
                switch (x.op) {

                    case IN :
                    case NOT_IN :
                    case EQUALS :
                    case NOT_EQUALS :
                    case LT :
                    case LTE :
                    case GT :
                    case GTE :
                    case NOT_LT :
                    case NOT_LTE :
                    case NOT_GT :
                    case NOT_GTE :
                        return true;
                    default :
                        return null;

                }
            }

            @Override
            public Boolean visit(ExprUnary x) throws Err {
                switch (x.op) {

                    case NOT :
                    case ALWAYS :
                    case AFTER :
                        return x.sub.accept(this);
                    case ONE :
                    case LONE :
                    case NO :
                    case SOME :
                        return true;
                    default :
                        return null;

                }
            }
        }) != null;
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        Set<ExprHasName> tmp = acts;
        if (!((x.op == ExprList.Op.AND && !univ) || (x.op == ExprList.Op.OR && univ))) {
            acts = new HashSet<ExprHasName>();

            List<Expr> resas = new ArrayList<>();
            for (Expr s : x.args)
                resas.add(s.accept(this));

            Expr res = ExprList.make(x.pos, x.closingBracket, x.op, resas);

            acts = tmp;
            return addSelf(res);

        } else {
            List<Expr> res = new ArrayList<>();
            for (Expr s : x.args)
                res.add(s.accept(this));

            x = ExprList.make(x.pos, x.closingBracket, x.op, res);
            return x;
        }
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        throw new RuntimeException();
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        return (x.cond.implies(x.left)).and(x.cond.not().implies(x.right)).accept(this);
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        throw new RuntimeException();
    }

    Map<ExprHasName,ExprHasName>      newvars   = new HashMap<ExprHasName,ExprHasName>();
    Map<Field,Map<ExprHasName,Field>> newfields = new HashMap<Field,Map<ExprHasName,Field>>();

    @Override
    public Expr visit(ExprQt x) throws Err {
        Set<ExprHasName> nacts = new HashSet<ExprHasName>();
        List<Decl> decls = new ArrayList<Decl>();
        for (Decl d : x.decls) {
            Sig tp = d.expr.type().fold().get(0).get(0);
            if (tp.isTrace != null) {
                if (d.names.size() == 1 || noSelfCompose) {
                    nacts.addAll(d.names);
                    vars.addAll(d.names);
                    newvars.put(d.names.get(0), d.names.get(0));
                    decls.add(d);
                } else {
                    Sig nsig = new PrimSig(tp.label + d.names.size(), tp.attributes.toArray(new Attr[tp.attributes.size()]));
                    for (Decl f : tp.getFieldDecls()) {
                        for (ExprHasName name : f.names) {
                            List<ExprHasName> names = new ArrayList<ExprHasName>();
                            for (ExprHasName sname : d.names)
                                names.add(ExprVar.make(f.span(), name.label + sname.label, f.get().type()));
                            Field[] nfields = nsig.addTrickyField(f.span(), f.isPrivate, f.disjoint, f.disjoint2, null, f.isVar, names, f.expr);
                            Map<ExprHasName,Field> new_fields = new HashMap<ExprHasName,Field>();
                            for (int i = 0; i < d.names.size(); i++)
                                new_fields.put(d.names.get(i), nfields[i]);
                            newfields.put((Field) name, new_fields);
                        }
                    }

                    Decl nvar = nsig.oneOf(d.names.toString());
                    for (ExprHasName e : d.names)
                        newvars.put(e, nvar.get());
                    vars.addAll(nvar.names);
                    nacts.addAll(nvar.names);
                    decls.add(nvar);
                }
            } else {
                decls.add(d);
            }
        }
        Expr sres;
        Set<ExprHasName> tmp = acts;
        boolean tmp_univ = univ;
        if (!nacts.isEmpty()) {
            if (x.op != Op.ALL && x.op != Op.SOME)
                throw new RuntimeException();

            acts = nacts;
            for (ExprHasName e : acts)
                extracts.computeIfAbsent(e, xx -> new ArrayList<Expr>());
            univ = x.op == Op.ALL;

            sres = x.sub.accept(this);

            acts = tmp;
            univ = tmp_univ;

        } else {
            acts = new HashSet<ExprHasName>();
            sres = x.sub.accept(this);
            acts = tmp;
        }
        Expr res = x.op.make(x.pos, x.closingBracket, decls, sres);

        return addSelf(res);
    }

    boolean toplevel = true;

    @Override
    public Expr visit(ExprUnary x) throws Err {
        Expr res;
        if (x.op == ExprUnary.Op.NOOP)
            return x.sub.accept(this);
        else {
            boolean tl = toplevel;
            toplevel = false;
            Set<ExprHasName> tmp = acts;
            acts = new HashSet<ExprHasName>();
            res = x.op.make(x.pos, x.sub.accept(this));
            acts = tmp;
            toplevel = tl;
            return addSelf(res);
        }

    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        if (newvars.containsKey(x))
            return newvars.get(x);
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Field x) throws Err {
        if (newfields.containsKey(x))
            if (current_new_var == null)
                throw new RuntimeException("Could not find context for self-composition: " + x);
            else
                return newfields.get(x).getOrDefault(current_new_var, x);
        return x;
    }

    @Override
    public Expr visit(Func x) throws Err {
        throw new RuntimeException();
    }

    @Override
    public Expr visit(Assert x) throws Err {
        throw new RuntimeException();
    }

    @Override
    public Expr visit(Macro macro) throws Err {
        throw new RuntimeException();
    }

}
