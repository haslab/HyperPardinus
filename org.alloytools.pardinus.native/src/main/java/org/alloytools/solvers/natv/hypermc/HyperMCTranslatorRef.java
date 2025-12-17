package org.alloytools.solvers.natv.hypermc;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class HyperMCTranslatorRef extends HyperMCSolverRef {

    private static final long serialVersionUID = 1L;

    public HyperMCTranslatorRef() {
        super(null);
    }

    @Override
    public String id() {
        return "electrod.hypermcts";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("a BMC for hyper-properties, generates SMV files for models and an HQ file with a hyper formula; models as a transition system with INIT/INVAR/TRANS");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/hypersmv/ah combination in some way";
    }

    @Override
    public boolean isPresent() {
        return electrod != null;
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod"
        };
    }

    @Override
    public boolean isTransformer() {
        return true;
    }
}
