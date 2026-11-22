# Shared virtual-gauge identities

Private `MPSTensor.twistedTensor_gaugeEquiv` and `MPSTensor.gauge_product_intertwines` in `MPS/Symmetry/OnSite/VirtualRepresentation.lean` are replaced by public lemmas of the same names in `MPS/Tensor/Gauge/OnSiteSymmetry.lean`; `MPS/Tensor/GlobalSymmetry.lean` reuses the latter. All existing public headers, imports and Blueprint anchors are retained. This implements rank 8 of the comprehensive audit: net −30 Lean lines.
