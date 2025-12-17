package org.alloytools.solvers.natv.hypermc;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class HyperMCAHRef extends HyperMCSolverRef {

    private static final long serialVersionUID = 1L;

    public HyperMCAHRef() {
        super("hypersmv");
    }

    @Override
    public String id() {
        return "hyper.autohyper";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("This is a solver based on the complete hyper model checker AutoHyper, with translations through electrod and hypersmv.");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/hypersmv/ah combination in some way";
    }

}
