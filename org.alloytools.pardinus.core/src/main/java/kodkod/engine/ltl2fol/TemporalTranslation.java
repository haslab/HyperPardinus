package kodkod.engine.ltl2fol;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.ltl2fol.TemporalTranslator.IterationStep;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.util.ints.IntSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TemporalTranslation extends Translation {
    
    Translation translation;
    private int traceLength;
    private PardinusBounds extbounds;
    private final List<IterationStep> previousSols = new ArrayList<IterationStep>();
    private Formula formula;
    public final Map<Object, Expression> reifs = new HashMap<Object, Expression>();
    private Formula reforms;
    private Formula extformula;
    private int past_depth;
    private boolean clear;
    TemporalInstance cand;
    Map<Formula,List<TemporalInstance>> adds;

    public TemporalTranslation(Translation translation, int traceLength, int past_depth, Formula extformula, PardinusBounds extbounds, Formula formula, PardinusBounds bounds, ExtendedOptions options, TemporalInstance cand, Map<Formula,List<TemporalInstance>> adds) {
        super(bounds, options);
        this.translation = translation;
        this.traceLength = traceLength;
        this.extbounds = extbounds;
        this.extformula = extformula;
        this.formula = formula;
        this.past_depth = past_depth;
        this.clear = false;
        this.cand = cand;
        this.adds = adds;
    }

    @Override
    public IntSet primaryVariables(Relation relation) {
        return translation.primaryVariables(relation);
    }

    @Override
    public int numPrimaryVariables() {
        return translation.numPrimaryVariables();
    }

    @Override  
    public boolean trivial() { return translation.trivial(); }

    public int traceLength() {
        return traceLength;
    }

    public PardinusBounds extBounds() {
        return extbounds;
    }
    
    public Formula extFormula() {
        return extformula;
    }
    
    @Override 
    public PardinusBounds bounds() {
        return (PardinusBounds) super.bounds();
    }
    
    @Override 
    public ExtendedOptions options() {
        return (ExtendedOptions) super.options();
    }
    
    public Formula formula() {
        return formula;
    }
    
    public TranslationLog log() {
        return translation instanceof Whole ? ((Whole) translation).log() : null;
    }
    
    @Override  
    public SATSolver cnf() {
        return translation.cnf();
    }

    public void addSeenSol(IterationStep newstep) {
        previousSols.add(newstep);
        // length of trace is state identifier + 1
        // this was at nextFormula but not nextSAT, check
//        traceLength = Integer.max(newstep.start + 1, 1);
    }

    public List<IterationStep> seenSols() {
        return previousSols;
    }

    public void clear() {
        clear = true;
    }

    public boolean isClear() {
        return clear;
    }

    public void removeSeenFromSols(int state) {
        previousSols.removeIf(s -> s.start > state);
        traceLength = Math.max(state, options().minTraceLength());
    }

    public void traceInc() {
        traceLength++;
        clear();
    }

    public void setReforms(Formula reforms) {
        this.reforms = reforms;
    }
    
    public Formula reforms() {
        return reforms;
    }

    public int pastDepth() {
        return past_depth;
    }

    public Instance interpretStatic() {
        return super.interpret(extbounds);
    }

    public void addSeenSol(List<IterationStep> seenSols) {
        previousSols.addAll(seenSols);
    }
    

}
