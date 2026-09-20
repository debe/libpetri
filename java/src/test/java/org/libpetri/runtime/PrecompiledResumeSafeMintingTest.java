package org.libpetri.runtime;

import org.libpetri.core.*;

import java.util.List;
import java.util.Map;

/** {@link AbstractResumeSafeMintingTest} against the production executor. */
class PrecompiledResumeSafeMintingTest extends AbstractResumeSafeMintingTest {
    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial,
        Map<String, List<Token<?>>> restore, String scope
    ) {
        var builder = PrecompiledNetExecutor.builder(net, initial);
        if (restore != null) builder.restore(restore);
        if (scope != null) builder.executionScope(scope);
        return builder.build();
    }

    @Override
    protected void pinScope(String scope) {
        PrecompiledNetExecutor.builder(PetriNet.builder("empty").build(), Map.of()).executionScope(scope);
    }
}
