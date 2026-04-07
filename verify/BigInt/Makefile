COQC ?= coqc

FILES := NTTTree.v NTTConvolution.v NTTSpectral.v NTTKernel.v NTTKernelBounded.v NTTConcrete.v BigIntMul.v
BIGINT_PROOF_FILES := BigIntMulProof.v BigIntMulCanonical.v BigIntMulCRT.v BigIntMulCRTArithmetic.v BigIntMulCRTExact.v BigIntMulCRTArrayExact.v BigIntMulCRTPrefix.v BigIntMulConvolutionBridge.v BigIntMulConvolutionCanonical.v BigIntMulConvolutionExact.v BigIntMulNormalize.v BigIntMulOpsProof.v BigIntMulTests.v BigIntMulNormalizeArray.v BigIntMulNormalizeArithmetic.v BigIntMulNormalizeInvariant.v BigIntMulNormalizeValue.v BigIntMulAlgebra.v BigIntMulCoefficients.v BigIntMulCyclic.v BigIntMulCompose.v BigIntMulCoeffExact.v BigIntMulCoeffExactFinal.v BigIntMulResidues.v BigIntMulScalarReduction.v BigIntMulPrime469Concrete.v BigIntMulPrime181Concrete.v BigIntMulCorrect.v BigIntMulFProof.v
CONCRETE_FACTS := NTTConcrete469Squares.v NTTConcrete469Inverse.v NTTConcrete469InvPow2.v NTTConcrete469Supported.v NTTConcrete181Squares.v NTTConcrete181Inverse.v NTTConcrete181InvPow2.v NTTConcrete181Supported.v
BENCH_SUPPORT := NTTTreeBench.v
BENCH_FILES := NTTTreeBench15.v
TEST_FILES := NTTTreeEquivTests.v BigIntMulTests.v

.PHONY: all clean bench15 bench-modpow concrete-facts test-equivalence test-bigint proof-bigint

all: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) -Q . BigInt $<

bench15: $(FILES:.v=.vo) $(BENCH_SUPPORT:.v=.vo) $(BENCH_FILES:.v=.vo)

bench-modpow:
	ulimit -s unlimited && $(COQC) -Q . BigInt ModPowBench.v

concrete-facts: $(FILES:.v=.vo) $(CONCRETE_FACTS:.v=.vo)

test-equivalence: $(FILES:.v=.vo) $(BENCH_SUPPORT:.v=.vo) $(TEST_FILES:.v=.vo)

test-bigint: $(FILES:.v=.vo) BigIntMulTests.vo

proof-bigint: $(FILES:.v=.vo) $(CONCRETE_FACTS:.v=.vo) $(BIGINT_PROOF_FILES:.v=.vo)

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
