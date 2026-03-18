package org.libpetri.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Sign-bit regression tests for CompiledNet bitmap helpers.
 * Java uses signed long (bit 63 is sign bit) — verify correct behaviour.
 */
class CompiledNetBitmapTest {

    @Test
    void containsAll_signBit() {
        long[] snapshot = { 1L << 63 };
        long[] mask = { 1L << 63 };
        assertTrue(CompiledNet.containsAll(snapshot, mask));
        assertFalse(CompiledNet.containsAll(new long[] { 0L }, mask));
    }

    @Test
    void intersects_signBit() {
        long[] snapshot = { 1L << 63 };
        long[] mask = { 1L << 63 };
        assertTrue(CompiledNet.intersects(snapshot, mask));
        assertFalse(CompiledNet.intersects(new long[] { 0L }, mask));
    }
}
