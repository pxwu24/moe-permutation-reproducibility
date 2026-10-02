# Lean proof sources

Sources are grouped by mathematical topic. The [project summary](../README.md) distinguishes unconditional results from deductions using the remaining convergence theorem.

| Folder | Content |
| --- | --- |
| [Preliminaries/](Preliminaries/) | Channels and matrix preliminaries |
| [HaarProjections/](HaarProjections/) | Haar projections and local support |
| [RandomCompression/](RandomCompression/) | Random compression and the Bernoulli spectral edge |
| [OutputStates/](OutputStates/) | Output state spaces |
| [BellOutput/](BellOutput/) | Bell outputs and normalized Choi moments |
| [Antisymmetric/](Antisymmetric/) | Antisymmetric postprocessing |
| [Entropy/](Entropy/) | Entropy estimates |
| [Nonadditivity/](Nonadditivity/) | Main nonadditivity theorem |
| [Dimension182/](Dimension182/) | Output dimension 182 and Appendix C |
| [StrongConvergence/](StrongConvergence/) | Partial formalization of strong convergence |
| [Checks/](Checks/) | Declaration checks and axiom audits |

[AllProofs.lean](AllProofs.lean) imports every maintained proof source. [Checks/AggregateAudit.lean](Checks/AggregateAudit.lean) audits all declarations.
