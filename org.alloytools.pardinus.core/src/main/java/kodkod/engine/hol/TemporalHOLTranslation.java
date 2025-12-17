package kodkod.engine.hol;

import kodkod.ast.Formula;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.ltl2fol.TemporalTranslation;
import kodkod.instance.PardinusBounds;

public class TemporalHOLTranslation extends TemporalTranslation {

	final public Proc proc;

	public TemporalHOLTranslation(Proc proc2, int traceLength, int past_depth, Formula extformula,
			PardinusBounds extbounds, Formula formula, PardinusBounds bounds, ExtendedOptions options) {
		super(null, traceLength,past_depth,extformula,extbounds,formula,bounds,options, null, null);
		this.proc = proc2;
	}

}
