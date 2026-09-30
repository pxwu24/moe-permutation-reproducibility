import Lake
open Lake DSL

package «projection-preliminaries»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib Preliminaries where
  roots := #[
    `Preliminaries,
    `PaperFormalization,
    `PreliminariesMatrix,
    `PreliminariesChoi,
    `PreliminariesLegendre,
    `PreliminariesAnalysis,
    `CompletePositivity,
    `BernoulliCalculus,
    `BernoulliDuality,
    `BernoulliEdgeCalculus,
    `BernoulliCriticalPoint,
    `CompressionSpectral,
    `CompressionExtension,
    `BlockModification,
    `ProjectionStrongConvergence,
    `GaussianRank,
    `GaussianRadial,
    `GaussianUnitary,
    `GaussianMatrixLaw,
    `HaarProjection,
    `HaarMeasure,
    `HaarOrbitUnique,
    `GaussianWhitening,
    `ProjectionOrbit,
    `MatrixRankMeasurable,
    `HaarLocalSupport,
    `HaarFullLocalSupport,
    `CauchyBernoulli,
    `CauchyHolomorphic,
    `SpectralEdge,
    `CauchyHolomorphy,
    `CauchyLocalInverse,
    `FullAudit,
    `K182Dual,
    `K182Numerics,
    `K182Entropy,
    `K182Audit,
    `UnprovedTargets]
