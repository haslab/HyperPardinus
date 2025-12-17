package org.alloytools.solvers.natv.hypermc;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class HyperMCHQRef extends HyperMCSolverRef {

    private static final long serialVersionUID = 1L;

    public HyperMCHQRef() {
        super("hypersmv");
    }

    @Override
    public String id() {
        return "hyper.hyperq";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("This is a solver based on the bounded hyper model checker HyperQ, with translations through electrod and hypersmv.");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/hypersmv/hq combination in some way";
    }

}
