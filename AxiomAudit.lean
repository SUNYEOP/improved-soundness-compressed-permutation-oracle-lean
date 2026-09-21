import QuantumOracle

-- These commands inspect dependencies, not the hypotheses of each theorem.
-- A conditional theorem can have only standard axioms and still require the
-- unproved mathematical premises displayed in its statement.
#print axioms QuantumOracle.Database.inverse_inverse
#print axioms QuantumOracle.Database.inverse_size
#print axioms QuantumOracle.Database.set_size_of_fresh
#print axioms QuantumOracle.Database.mem_block_iff
#print axioms QuantumOracle.Database.block_base_unique
#print axioms QuantumOracle.Database.inverse_ofPermutation
#print axioms QuantumOracle.BasisLookup.ordinary_defined
#print axioms QuantumOracle.BasisLookup.marked_defined
#print axioms QuantumOracle.BasisLookup.ordinary_involutive
#print axioms QuantumOracle.BasisLookup.marked_involutive
#print axioms QuantumOracle.BasisLookup.inverseOrdinary_defined
#print axioms QuantumOracle.BasisLookup.inverseMarked_defined
#print axioms QuantumOracle.BasisLookup.controlled_true
#print axioms QuantumOracle.Query.linearLift_single
#print axioms QuantumOracle.Query.ordinaryLookup_isometry
#print axioms QuantumOracle.Query.markedLookup_defined
#print axioms QuantumOracle.Query.exactOrdinary_basis_action
#print axioms QuantumOracle.Query.exactMarked_basis_action
#print axioms QuantumOracle.Query.controlled_isometry
#print axioms QuantumOracle.Query.indexed_isometry
#print axioms QuantumOracle.CompressionIndex.card_fresh
#print axioms QuantumOracle.CompressionIndex.fresh_nonempty
#print axioms QuantumOracle.CompressionIndex.databaseEquiv
#print axioms QuantumOracle.UniformState.uniform_norm
#print axioms QuantumOracle.UniformState.extensionUniform_norm
#print axioms QuantumOracle.orthonormalSwap_left
#print axioms QuantumOracle.orthonormalSwap_fixed
#print axioms QuantumOracle.CompressionBlock.compression_empty
#print axioms QuantumOracle.CompressionBlock.compression_involutive
#print axioms QuantumOracle.BlockOperator.transport_involutive
#print axioms QuantumOracle.Compression.pC_isometry
#print axioms QuantumOracle.Compression.pC_involutive
#print axioms QuantumOracle.Compression.plusState_eq_manuscript
#print axioms QuantumOracle.Compression.pC_ket_base
#print axioms QuantumOracle.Compression.pC_plusState
#print axioms QuantumOracle.Compression.pC_embedBlock_fixed
#print axioms QuantumOracle.CompressedQuery.ordinary_isometry
#print axioms QuantumOracle.CompressedQuery.markedTwoSided_isometry
#print axioms QuantumOracle.CompressedQuery.ordinary_involutive
#print axioms QuantumOracle.CompressedQuery.marked_involutive
#print axioms QuantumOracle.CompressedQuery.inverseOrdinary_involutive
#print axioms QuantumOracle.CompressedQuery.inverseMarked_involutive
#print axioms QuantumOracle.BlockSupport.supported_succ_of_preservesBlocks
#print axioms QuantumOracle.CompressedSupport.compression_preservesBlocks
#print axioms QuantumOracle.CompressedSupport.ordinary_supported
#print axioms QuantumOracle.CompressedSupport.marked_supported
#print axioms QuantumOracle.CompressedSupport.inverseOrdinary_supported
#print axioms QuantumOracle.CompressedSupport.inverseMarked_supported
#print axioms QuantumOracle.CompressedSupport.controlledOrdinaryTwoSided_supported
#print axioms QuantumOracle.CompressedSupport.controlledMarkedTwoSided_supported
#print axioms QuantumOracle.CompressedSupport.ordinary_schedule_supported
#print axioms QuantumOracle.PermutationExtensions.definedEquiv
#print axioms QuantumOracle.PermutationExtensions.extensionsEquivUnused
#print axioms QuantumOracle.PermutationExtensions.card_extensions
#print axioms QuantumOracle.PermutationExtensions.exists_extension
#print axioms QuantumOracle.PermutationExtensions.card_edgeFiber
#print axioms QuantumOracle.PermutationExtensions.extensions_card_eq_mul_edgeFiber
#print axioms QuantumOracle.ConsistentState.vector_norm
#print axioms QuantumOracle.ConsistentState.vector_empty_eq_uniform
#print axioms QuantumOracle.ConsistentState.vector_inverse_apply
#print axioms QuantumOracle.ConsistentState.inner_vector_eq_card_common
#print axioms QuantumOracle.ConsistentState.answerProjection_vector_of_fresh
#print axioms QuantumOracle.ConsistentState.answerProjection_vector_fresh_norm_sq
#print axioms QuantumOracle.ConsistentState.answerProjection_vector_of_occupied
#print axioms QuantumOracle.ConsistentState.sum_answerProjection
#print axioms QuantumOracle.CommonDatabases.commonLevelEquiv
#print axioms QuantumOracle.CommonDatabases.card_commonLevel_fixedPoints
#print axioms QuantumOracle.CommonDatabases.card_commonLevel_relabel
#print axioms QuantumOracle.FiniteIncidence.kernel_entry
#print axioms QuantumOracle.FiniteIncidence.gram_operator
#print axioms QuantumOracle.ExtensionOperator.T_single
#print axioms QuantumOracle.ExtensionOperator.gramMatrix_entry_fixedPoints
#print axioms QuantumOracle.ExtensionOperator.gramMatrix_operator
#print axioms QuantumOracle.ExtensionOperator.T_adjoint_basis_entry
#print axioms QuantumOracle.ExtensionOperator.gramMatrix_relabel
#print axioms QuantumOracle.KernelEquivariance.matrix_commutes_of_relabel
#print axioms QuantumOracle.KernelEquivariance.relabelOperator_single
#print axioms QuantumOracle.KernelEquivariance.gramMatrix_commutes
#print axioms QuantumOracle.KernelEquivariance.T_adjoint_commutes
#print axioms QuantumOracle.KnowledgeSpace.range_T
#print axioms QuantumOracle.KnowledgeSpace.le_succ
#print axioms QuantumOracle.KnowledgeSpace.mono
#print axioms QuantumOracle.KnowledgeSpace.full_eq_top
#print axioms QuantumOracle.KnowledgeSpace.eq_bot_of_gt
#print axioms QuantumOracle.KnowledgeSpace.zero_eq_span_uniform
#print axioms QuantumOracle.GramRange.range_comp_adjoint
#print axioms QuantumOracle.GramRange.range_T_comp_adjoint
#print axioms QuantumOracle.ConsistencyGrowth.answerProjection_vector_eq_smul
#print axioms QuantumOracle.ConsistencyGrowth.answerProjection_map_K_le
#print axioms QuantumOracle.ConsistencyGrowth.inverseAnswerProjection_eq
#print axioms QuantumOracle.ConsistencyGrowth.inverseAnswerProjection_map_K_le
#print axioms QuantumOracle.ExtensionResolution.sum_extensions
#print axioms QuantumOracle.ExtensionResolution.sum_inner_extensions_eq_zero
#print axioms QuantumOracle.ExtensionResolution.sum_inner_extensions_eq_zero'
#print axioms QuantumOracle.WorkspaceKnowledge.slice_onWorkspace
#print axioms QuantumOracle.WorkspaceKnowledge.supported_onWorkspace
#print axioms QuantumOracle.WorkspaceKnowledge.supported_productState
#print axioms QuantumOracle.WorkspaceKnowledge.norm_onWorkspace
#print axioms QuantumOracle.AnswerSelection.select_eq_sum
#print axioms QuantumOracle.AnswerSelection.select_mem_succ
#print axioms QuantumOracle.ExactCoherentQuery.query_single
#print axioms QuantumOracle.ExactCoherentQuery.query_involutive
#print axioms QuantumOracle.ExactCoherentQuery.markedSlice_query_enabled
#print axioms QuantumOracle.ExactCoherentQuery.ordinarySlice_query_enabled
#print axioms QuantumOracle.ExactCoherentQuery.markedSlice_query_disabled
#print axioms QuantumOracle.ExactQueryGrowth.query_supported
#print axioms QuantumOracle.ExactQueryGrowth.liftedQuery_supported
#print axioms QuantumOracle.ExactQueryGrowth.liftedQuery_supported_min
#print axioms QuantumOracle.ExactExecution.initialIsometry
#print axioms QuantumOracle.ExactExecution.initial_supported
#print axioms QuantumOracle.ExactExecution.run_norm
#print axioms QuantumOracle.ExactExecution.run_normalized
#print axioms QuantumOracle.ExactExecution.run_supported
#print axioms QuantumOracle.ExactExecution.run_supported_of_le
#print axioms QuantumOracle.HiddenIsometry.onOracle
#print axioms QuantumOracle.HiddenIsometry.norm_onOracle
#print axioms QuantumOracle.HiddenIsometry.reduced_onOracle
#print axioms QuantumOracle.HiddenIsometry.reducedState_onOracle
#print axioms QuantumOracle.HiddenIsometry.onOracle_onWorkspace
#print axioms QuantumOracle.HiddenIsometry.onOracle_productState
#print axioms QuantumOracle.ExactFinalState.reduced_eq_gram
#print axioms QuantumOracle.ExactFinalState.reduced_posSemidef
#print axioms QuantumOracle.ExactFinalState.trace_reduced
#print axioms QuantumOracle.ExactFinalState.finalReduced_posSemidef
#print axioms QuantumOracle.ExactFinalState.finalReduced_isHermitian
#print axioms QuantumOracle.ExactFinalState.finalReduced_trace_one
#print axioms QuantumOracle.CompressedCoherentQuery.markedSlice_query_forward
#print axioms QuantumOracle.CompressedCoherentQuery.markedSlice_query_inverse
#print axioms QuantumOracle.CompressedCoherentQuery.ordinarySlice_query_enabled
#print axioms QuantumOracle.CompressedCoherentQuery.markedSlice_query_disabled
#print axioms QuantumOracle.CompressedCoherentQuery.query_supported
#print axioms QuantumOracle.CompressedCoherentQuery.liftedQuery_supported
#print axioms QuantumOracle.CompressedCoherentQuery.liftedQuery_norm
#print axioms QuantumOracle.CompressedExecution.initialIsometry
#print axioms QuantumOracle.CompressedExecution.initial_eq_productState
#print axioms QuantumOracle.CompressedExecution.supported_onWorkspace
#print axioms QuantumOracle.CompressedExecution.run_norm
#print axioms QuantumOracle.CompressedExecution.run_normalized
#print axioms QuantumOracle.CompressedExecution.run_supported
#print axioms QuantumOracle.CompressedExecution.run_supported_min
#print axioms QuantumOracle.CompressedExecution.finalReduced_posSemidef
#print axioms QuantumOracle.CompressedExecution.finalReduced_isHermitian
#print axioms QuantumOracle.CompressedExecution.finalReduced_trace_one
#print axioms QuantumOracle.FinitePurification.reducedState_coordinateState
#print axioms QuantumOracle.FinitePurification.anyHidden
#print axioms QuantumOracle.FinitePurification.sameSpace_distance
#print axioms QuantumOracle.FinitePurification.purificationDistance_self
#print axioms QuantumOracle.FinitePurification.purificationDistance_le_hiddenIsometry
#print axioms QuantumOracle.ProductReduction.reduced_productState_eq
#print axioms QuantumOracle.ConcreteExperiment.exists_algorithm_le
#print axioms QuantumOracle.ConcreteExperiment.purification
#print axioms QuantumOracle.ConcreteExperiment.family
#print axioms QuantumOracle.ConcreteExperiment.dist_def
#print axioms QuantumOracle.ConcreteExperiment.distances_bddAbove
#print axioms QuantumOracle.ConcreteExperiment.dist_nonneg
#print axioms QuantumOracle.ConcreteExperiment.dist_le_two
#print axioms QuantumOracle.ConcreteExperiment.dist_mono
#print axioms QuantumOracle.ConcreteExperiment.final_eq_of_zero_queries
#print axioms QuantumOracle.ConcreteExperiment.dist_zero
#print axioms QuantumOracle.ConcreteExperiment.dist_le_of_hidden_comparison
#print axioms QuantumOracle.ConcreteHybrid.initial_transport
#print axioms QuantumOracle.ConcreteHybrid.run_error_le
#print axioms QuantumOracle.ConcreteHybrid.vector_error_le
#print axioms QuantumOracle.ConcreteHybrid.dist_le_of_local_error
#print axioms QuantumOracle.OutputDiscard.discardIsometry
#print axioms QuantumOracle.OutputDiscard.norm_discardVector_sub
#print axioms QuantumOracle.OutputDiscard.reducedFin_discardVector
#print axioms QuantumOracle.OutputDiscard.discardMatrix_keepAll
#print axioms QuantumOracle.DiscardDistance.reducedFin_restoreWorkspace
#print axioms QuantumOracle.DiscardDistance.discardPurification
#print axioms QuantumOracle.DiscardDistance.discardPurification_distance
#print axioms QuantumOracle.DiscardDistance.purificationDistance_discard_le
#print axioms QuantumOracle.FiniteDensity.reducedFin_posSemidef
#print axioms QuantumOracle.FiniteDensity.reducedFin_isHermitian
#print axioms QuantumOracle.FiniteDensity.trace_reducedFin
#print axioms QuantumOracle.FiniteDensity.trace_reducedFin_of_normalized
#print axioms QuantumOracle.OutputExperiment.exactVector_normalized
#print axioms QuantumOracle.OutputExperiment.compressedVector_normalized
#print axioms QuantumOracle.OutputExperiment.exactFinal_eq_discardMatrix
#print axioms QuantumOracle.OutputExperiment.compressedFinal_eq_discardMatrix
#print axioms QuantumOracle.OutputExperiment.exactFinal_posSemidef
#print axioms QuantumOracle.OutputExperiment.compressedFinal_posSemidef
#print axioms QuantumOracle.OutputExperiment.exactFinal_isHermitian
#print axioms QuantumOracle.OutputExperiment.compressedFinal_isHermitian
#print axioms QuantumOracle.OutputExperiment.exactFinal_trace_one
#print axioms QuantumOracle.OutputExperiment.compressedFinal_trace_one
#print axioms QuantumOracle.OutputExperiment.purification
#print axioms QuantumOracle.OutputExperiment.family
#print axioms QuantumOracle.OutputExperiment.dist_def
#print axioms QuantumOracle.OutputExperiment.algorithm_distance_le_retained
#print axioms QuantumOracle.OutputExperiment.dist_eq_retained
#print axioms QuantumOracle.OutputExperiment.dist_zero
#print axioms QuantumOracle.OutputExperiment.dist_le_of_local_error
#print axioms QuantumOracle.HarmonicLayers.K_succ_eq_sup
#print axioms QuantumOracle.HarmonicLayers.orthogonal_of_lt
#print axioms QuantumOracle.HarmonicLayers.K_eq_iSup
#print axioms QuantumOracle.HarmonicLayers.iSup_eq_top
#print axioms QuantumOracle.HarmonicLayers.orthogonalFamily
#print axioms QuantumOracle.HarmonicLayers.sum_projection
#print axioms QuantumOracle.AdjointCoefficients.adjoint_apply
#print axioms QuantumOracle.AdjointCoefficients.sum_adjoint_extensions_eq_zero
#print axioms QuantumOracle.AdjointCoefficients.adjoint_injective_on_knowledge
#print axioms QuantumOracle.AdjointCoefficients.norm_adjoint_pos_of_mem
#print axioms QuantumOracle.GramFiltration.adjoint_gram
#print axioms QuantumOracle.GramFiltration.range_gram
#print axioms QuantumOracle.GramFiltration.ker_gram
#print axioms QuantumOracle.GramFiltration.re_inner_gram_pos
#print axioms QuantumOracle.GramFiltration.gramLinearEquiv
#print axioms QuantumOracle.GramFiltration.gram_eq_sum_relabel
#print axioms QuantumOracle.GramFiltration.gram_commutes
#print axioms QuantumOracle.GramFiltration.gram_mem_knowledge
#print axioms QuantumOracle.GramFiltration.gram_mem_orthogonal
#print axioms QuantumOracle.GramFiltration.gram_mem_layer
#print axioms QuantumOracle.HarmonicGram.gramOnLayer_isSelfAdjoint
#print axioms QuantumOracle.HarmonicGram.re_inner_gramOnLayer_pos
#print axioms QuantumOracle.HarmonicGram.gramLayerEquiv
#print axioms QuantumOracle.HarmonicGram.gramOnLayer_commutes
#print axioms QuantumOracle.LevelEmbedding.embed
#print axioms QuantumOracle.LevelEmbedding.inner_embed_of_ne
#print axioms QuantumOracle.CompressionCancellation.pC_definedPart
#print axioms QuantumOracle.CompressionCancellation.coordinates_pC_undefinedPart
#print axioms QuantumOracle.CompressionCancellation.pC_eq_defined_add
#print axioms QuantumOracle.CompressionCancellation.pC_apply_base
#print axioms QuantumOracle.CompressionCancellation.pC_apply_extension
#print axioms QuantumOracle.RawHarmonic.raw_apply_of_size
#print axioms QuantumOracle.RawHarmonic.raw_eq_zero_iff_of_mem
#print axioms QuantumOracle.RawHarmonic.raw_cancels
#print axioms QuantumOracle.RawHarmonic.pC_definedPart_raw
#print axioms QuantumOracle.RawHarmonic.pC_raw_supported_two_levels
#print axioms QuantumOracle.RawHarmonic.raw_zero_uniform
#print axioms QuantumOracle.RawEmbedding.total_injective
#print axioms QuantumOracle.RawEmbedding.total_cancels
#print axioms QuantumOracle.RawEmbedding.total_uniform
#print axioms QuantumOracle.RawEmbedding.total_adjoint_empty
#print axioms QuantumOracle.RawEmbedding.total_gram_uniform
#print axioms QuantumOracle.MatrixPolar.gramSqrt_posDef
#print axioms QuantumOracle.MatrixPolar.gramSqrt_mul_self
#print axioms QuantumOracle.MatrixPolar.commute_gramSqrt
#print axioms QuantumOracle.MatrixPolar.gramSqrt_mulVec_of_gram_fixed
#print axioms QuantumOracle.MatrixPolar.normalize_mulVec_of_gram_fixed
#print axioms QuantumOracle.MatrixPolar.normalize_conjTranspose_mul
#print axioms QuantumOracle.MatrixPolar.normalize_adjoint_comp
#print axioms QuantumOracle.MatrixPolar.isometry
#print axioms QuantumOracle.MatrixPolar.range_isometry
#print axioms QuantumOracle.PolarEmbedding.matrix_entry
#print axioms QuantumOracle.PolarEmbedding.matrix_mulVec_injective
#print axioms QuantumOracle.PolarEmbedding.candidate
#print axioms QuantumOracle.PolarEmbedding.candidate_uniform
#print axioms QuantumOracle.PolarEmbedding.range_candidate
#print axioms QuantumOracle.PolarEmbedding.candidate_cancels
#print axioms QuantumOracle.PolarEmbedding.pC_definedPart_candidate
#print axioms QuantumOracle.PolarEmbedding.pC_candidate_apply_base
#print axioms QuantumOracle.PolarComparison.run_error_le
#print axioms QuantumOracle.PolarComparison.vector_error_le
#print axioms QuantumOracle.PolarComparison.dist_le_of_local_error
#print axioms QuantumOracle.DatabaseDegree.project_eq_self_iff
#print axioms QuantumOracle.DatabaseDegree.project_isSymmetric
#print axioms QuantumOracle.DatabaseDegree.project_project
#print axioms QuantumOracle.DatabaseDegree.raw_mem
#print axioms QuantumOracle.RawDegree.total_of_mem_H
#print axioms QuantumOracle.RawDegree.total_adjoint_raw
#print axioms QuantumOracle.RawDegree.total_adjoint_total_of_mem_H
#print axioms QuantumOracle.RawDegree.domainGram_mem_H
#print axioms QuantumOracle.RawDegree.domainGram_commutes_projection
#print axioms QuantumOracle.PolarIntertwining.gram_commute_of_intertwines
#print axioms QuantumOracle.PolarIntertwining.inverse_gramSqrt_commute
#print axioms QuantumOracle.PolarIntertwining.normalize_intertwines_of_gram_commute
#print axioms QuantumOracle.PolarIntertwining.normalize_intertwines
#print axioms QuantumOracle.PolarIntertwining.isometry_fixed
#print axioms QuantumOracle.PolarIntertwining.isometry_maps_range
#print axioms QuantumOracle.PolarDegree.domainProjection_isHermitian
#print axioms QuantumOracle.PolarDegree.databaseProjection_isHermitian
#print axioms QuantumOracle.PolarDegree.matrix_intertwines_projection
#print axioms QuantumOracle.PolarDegree.candidate_intertwines_projection
#print axioms QuantumOracle.PolarDegree.candidate_mem_exactLevel
#print axioms QuantumOracle.PolarDegree.candidate_apply_eq_zero_of_mem_K
#print axioms QuantumOracle.PolarDegree.pC_candidate_supported_two_levels
#print axioms QuantumOracle.InversionSymmetry.oracle_vector
#print axioms QuantumOracle.InversionSymmetry.oracle_mem_K
#print axioms QuantumOracle.InversionSymmetry.oracle_mem_H
#print axioms QuantumOracle.InversionSymmetry.oracle_projection
#print axioms QuantumOracle.InversionSymmetry.raw_intertwines
#print axioms QuantumOracle.InversionSymmetry.total_intertwines
#print axioms QuantumOracle.PolarInversion.oracleMatrix_isHermitian
#print axioms QuantumOracle.PolarInversion.databaseMatrix_isHermitian
#print axioms QuantumOracle.PolarInversion.candidate_intertwines_linearMap
#print axioms QuantumOracle.PolarInversion.candidate_cancels_inverse
#print axioms QuantumOracle.PolarInversion.pC_definedPart_candidate_inverse
#print axioms QuantumOracle.EmbeddedExecution.supported_onOracle
#print axioms QuantumOracle.EmbeddedExecution.run_norm
#print axioms QuantumOracle.EmbeddedExecution.run_normalized
#print axioms QuantumOracle.EmbeddedExecution.run_supported_min
#print axioms QuantumOracle.EmbeddedExecution.reduced_run
#print axioms QuantumOracle.EmbeddedExecution.afterQuery_norm
#print axioms QuantumOracle.EmbeddedExecution.afterQuery_normalized
#print axioms QuantumOracle.EmbeddedExecution.afterQuery_supported_min
#print axioms QuantumOracle.EmbeddedExecution.reduced_afterQuery
#print axioms QuantumOracle.PolarEigenvector.gramSqrt_mulVec_of_eigenvector
#print axioms QuantumOracle.PolarEigenvector.inverse_gramSqrt_mulVec_of_eigenvector
#print axioms QuantumOracle.PolarEigenvector.normalize_mulVec_of_eigenvector
#print axioms QuantumOracle.PolarEigenvector.isometry_apply_of_gram_eigenvector
#print axioms QuantumOracle.PolarSpectrum.eigenvalue_pos
#print axioms QuantumOracle.PolarSpectrum.candidate_of_gram_eigen_pos
#print axioms QuantumOracle.PolarSpectrum.candidate_of_gram_eigen
#print axioms QuantumOracle.DatabaseRelabel.equiv
#print axioms QuantumOracle.DatabaseRelabel.operator
#print axioms QuantumOracle.DatabaseRelabel.relabel_size
#print axioms QuantumOracle.DatabaseRelabel.extends_relabel_iff
#print axioms QuantumOracle.DatabaseRelabel.vector_relabel_apply
#print axioms QuantumOracle.RelabelSymmetry.oracle_vector
#print axioms QuantumOracle.RelabelSymmetry.oracle_mem_H
#print axioms QuantumOracle.RelabelSymmetry.oracle_projection
#print axioms QuantumOracle.RelabelSymmetry.raw_intertwines
#print axioms QuantumOracle.RelabelSymmetry.total_intertwines
#print axioms QuantumOracle.PolarUnitary.gram_commute_of_unitary_intertwines
#print axioms QuantumOracle.PolarUnitary.normalize_intertwines
#print axioms QuantumOracle.PolarUnitary.isometry_intertwines
#print axioms QuantumOracle.PolarRelabel.candidate_intertwines_linearMap
#print axioms QuantumOracle.PolarRelabel.candidate_apply_relabel
#print axioms QuantumOracle.PolarRelabel.candidate_cancels_relabel
#print axioms QuantumOracle.ResidualPermutation.insert_remove
#print axioms QuantumOracle.ResidualPermutation.remove_insert
#print axioms QuantumOracle.ResidualPermutation.fiberEquiv
#print axioms QuantumOracle.ResidualPermutation.answerProductEquiv
#print axioms QuantumOracle.ResidualPermutation.insert_symm
#print axioms QuantumOracle.ResidualPermutation.reindex
#print axioms QuantumOracle.ResidualDatabase.insert_size
#print axioms QuantumOracle.ResidualDatabase.insert_injective
#print axioms QuantumOracle.ResidualDatabase.disjoint_ranges
#print axioms QuantumOracle.ResidualDatabase.jointInsert_injective
#print axioms QuantumOracle.ResidualDatabase.jointIota
#print axioms QuantumOracle.ResidualDatabase.jointIota_apply_insert
#print axioms QuantumOracle.ResidualConsistency.extends_insert_iff
#print axioms QuantumOracle.ResidualConsistency.amplitude_insert
#print axioms QuantumOracle.ResidualConsistency.vector_insert_apply
#print axioms QuantumOracle.ResidualConsistency.vector_insert_apply_of_answer_ne
#print axioms QuantumOracle.ResidualConsistency.reindex_vector_insert
#print axioms QuantumOracle.Conditioning.J
#print axioms QuantumOracle.Conditioning.J_apply_insert
#print axioms QuantumOracle.Conditioning.J_apply_of_undefined
#print axioms QuantumOracle.Conditioning.J_norm
#print axioms QuantumOracle.Conditioning.J_inner
#print axioms QuantumOracle.Conditioning.D
#print axioms QuantumOracle.Conditioning.D_apply_candidate
#print axioms QuantumOracle.Conditioning.D_norm
#print axioms QuantumOracle.Conditioning.candidate_adjoint_candidate
#print axioms QuantumOracle.Conditioning.D_eq_J_adjoint
#print axioms QuantumOracle.ConditioningQuery.ordinary_intertwines
#print axioms QuantumOracle.ConditioningQuery.marked_intertwines
#print axioms QuantumOracle.ConditioningInverse.JInverse
#print axioms QuantumOracle.ConditioningInverse.JInverse_norm
#print axioms QuantumOracle.ConditioningInverse.JInverse_apply_of_unattained
#print axioms QuantumOracle.ConditioningInverse.ordinary_intertwines
#print axioms QuantumOracle.ConditioningInverse.marked_intertwines
#print axioms QuantumOracle.ConditioningInitialization.uniform_amplitude_split
#print axioms QuantumOracle.ConditioningInitialization.uniform_slice
#print axioms QuantumOracle.ConditioningInitialization.J_uniform_eq_sum
#print axioms QuantumOracle.ConditioningInitialization.J_uniform_eq_plusState
#print axioms QuantumOracle.ConditioningInitialization.J_uniform_eq_pC_empty
#print axioms QuantumOracle.ConditioningComparison.error_nonneg
#print axioms QuantumOracle.ConditioningComparison.ordinary_error_le
#print axioms QuantumOracle.ConditioningComparison.marked_error_le
#print axioms QuantumOracle.ResidualRemoval.remove
#print axioms QuantumOracle.ResidualRemoval.mem_remove
#print axioms QuantumOracle.ResidualRemoval.remove_insert
#print axioms QuantumOracle.ResidualRemoval.insert_remove
#print axioms QuantumOracle.ResidualRemoval.size_remove_add_one
#print axioms QuantumOracle.ResidualRemoval.size_remove_le
#print axioms QuantumOracle.ResidualRemoval.mem_range_jointInsert_iff
#print axioms QuantumOracle.ResidualAdjoint.restrict
#print axioms QuantumOracle.ResidualAdjoint.adjoin
#print axioms QuantumOracle.ResidualAdjoint.inner_vector_insert
#print axioms QuantumOracle.ResidualAdjoint.adjoin_vector
#print axioms QuantumOracle.ResidualAdjoint.adjoin_mem_K
#print axioms QuantumOracle.ResidualAdjoint.restrict_mem_orthogonal
#print axioms QuantumOracle.ResidualAdjoint.restrict_answerProjection
#print axioms QuantumOracle.ResidualKnowledge.answerProjection_vector_eq_smul_recording
#print axioms QuantumOracle.ResidualKnowledge.restrict_vector_insert
#print axioms QuantumOracle.ResidualKnowledge.restrict_vector_of_mem
#print axioms QuantumOracle.ResidualKnowledge.restrict_vector_eq_smul
#print axioms QuantumOracle.ResidualKnowledge.restrict_vector_mem_K
#print axioms QuantumOracle.ResidualKnowledge.restrict_map_K_le
#print axioms QuantumOracle.ResidualKnowledge.restrict_mem_K
#print axioms QuantumOracle.ResidualKnowledge.restrict_mem_K_of_le
#print axioms QuantumOracle.ResidualLayers.mem_two_layers_of_mem_K
#print axioms QuantumOracle.ResidualLayers.mem_two_layers_of_mem_K_min
#print axioms QuantumOracle.ResidualLayers.knowledge_one_le_two_layers
#print axioms QuantumOracle.ResidualLayers.restrict_mem_zero
#print axioms QuantumOracle.ResidualLayers.restrict_mem_two_layers
#print axioms QuantumOracle.ResidualLayers.restrict_decomposition
#print axioms QuantumOracle.PolarOrthogonal.candidate_apply_projection
#print axioms QuantumOracle.PolarOrthogonal.candidate_apply_eq_zero_of_orthogonal_size
#print axioms QuantumOracle.PolarOrthogonal.candidate_apply_eq_zero_of_orthogonal_K
#print axioms QuantumOracle.PolarOrthogonal.candidate_mem_exactLevel_iff
#print axioms QuantumOracle.ConditioningDegree.J_apply_eq_zero_of_mem_K
#print axioms QuantumOracle.ConditioningDegree.J_apply_eq_zero_of_low_size
#print axioms QuantumOracle.ConditioningDegree.J_supported_two_levels
#print axioms QuantumOracle.ConditioningDegree.JInverse_supported_two_levels
#print axioms QuantumOracle.ConditioningDegree.D_supported_two_levels
#print axioms QuantumOracle.ConditioningInverseComparison.onOracle_candidate_inversion
#print axioms QuantumOracle.ConditioningInverseComparison.inverse_ordinary_error_eq
#print axioms QuantumOracle.ConditioningInverseComparison.inverse_marked_error_eq
#print axioms QuantumOracle.ConditioningInverseComparison.inverse_ordinary_error_le
#print axioms QuantumOracle.ConditioningInverseComparison.inverse_marked_error_le
#print axioms QuantumOracle.suffix_isometry
#print axioms QuantumOracle.hybrid_neighbor_dist_le
#print axioms QuantumOracle.evolution_dist_le
#print axioms QuantumOracle.conditioning_one_query_dist_le
#print axioms QuantumOracle.conditional_one_query_four_div_sqrt
#print axioms QuantumOracle.conditional_evolution_four_mul_div_sqrt_of_query_range
#print axioms QuantumOracle.le_two_div_sqrt_of_sq_le
#print axioms QuantumOracle.conditional_error_le_of_overlap
#print axioms QuantumOracle.first_row_scalar_bound
#print axioms QuantumOracle.tail_corner_scalar_bound
#print axioms QuantumOracle.one_sub_prod_one_sub_le_sum
#print axioms QuantumOracle.isometry_norm_sub_sq_of_re_overlap
#print axioms QuantumOracle.isometry_norm_sub_sq_of_scalar_overlap
#print axioms QuantumOracle.conditional_isometry_error_le_of_overlap
#print axioms QuantumOracle.CommonPurification.distance_le_two
#print axioms QuantumOracle.purificationDistance_le_witness
#print axioms QuantumOracle.purificationDistance_nonneg
#print axioms QuantumOracle.ExperimentFamily.dist_le_of_witnesses
#print axioms QuantumOracle.PurifiedRunPair.conditional_distance_le
#print axioms QuantumOracle.ExperimentFamily.conditional_soundness
#print axioms QuantumOracle.ExperimentFamily.conditional_soundness_in_range

-- The full type exposes every conditional premise in the main assembly step.
#check @QuantumOracle.ExperimentFamily.conditional_soundness_in_range

-- Concrete oracle growth has only the input-support premise.
#check @QuantumOracle.CompressedSupport.controlledMarkedTwoSided_supported

-- The exact extension kernel and indicator growth have no spectral premises.
#check @QuantumOracle.ExtensionOperator.T_adjoint_basis_entry
#check @QuantumOracle.ConsistencyGrowth.answerProjection_map_K_le

-- Actual executions: no oracle-growth assumption is supplied by the caller.
#check @QuantumOracle.ExactExecution.run_supported
#check @QuantumOracle.ExactExecution.run_normalized
#check @QuantumOracle.HiddenIsometry.reduced_onOracle
#check @QuantumOracle.ExactFinalState.finalReduced_trace_one
#check @QuantumOracle.ConcreteExperiment.dist_def
#check @QuantumOracle.ConcreteExperiment.dist_le_of_hidden_comparison
#check @QuantumOracle.ConcreteHybrid.dist_le_of_local_error

-- Discard any finite workspace factor; the infimum is over all witnesses.
#check @QuantumOracle.DiscardDistance.purificationDistance_discard_le
#check @QuantumOracle.OutputExperiment.dist_eq_retained
#check @QuantumOracle.OutputExperiment.dist_le_of_local_error

-- The positive polar isometry and its actual initial identity are constructed.
#check @QuantumOracle.PolarEmbedding.candidate_uniform
#check @QuantumOracle.PolarComparison.dist_le_of_local_error

-- Actual normalized degree and inversion identities have no spectral premises.
#check @QuantumOracle.RawDegree.total_adjoint_total_of_mem_H
#check @QuantumOracle.PolarDegree.candidate_mem_exactLevel
#check @QuantumOracle.PolarDegree.candidate_apply_eq_zero_of_mem_K
#check @QuantumOracle.PolarDegree.pC_candidate_supported_two_levels
#check @QuantumOracle.PolarInversion.candidate_intertwines
#check @QuantumOracle.EmbeddedExecution.run_supported_min
#check @QuantumOracle.EmbeddedExecution.afterQuery_supported_min

-- Scalar normalization requires the displayed actual Gram eigenvector equation.
#check @QuantumOracle.PolarEigenvector.isometry_apply_of_gram_eigenvector
#check @QuantumOracle.PolarSpectrum.candidate_of_gram_eigen

-- Full actual relabeling and residual conditioning are constructed internally.
#check @QuantumOracle.PolarRelabel.candidate_intertwines
#check @QuantumOracle.Conditioning.J
#check @QuantumOracle.Conditioning.J_norm
#check @QuantumOracle.Conditioning.D
#check @QuantumOracle.Conditioning.D_apply_candidate
#check @QuantumOracle.ConditioningQuery.ordinary_intertwines
#check @QuantumOracle.ConditioningQuery.marked_intertwines
#check @QuantumOracle.ConditioningInverse.ordinary_intertwines
#check @QuantumOracle.ConditioningInverse.marked_intertwines
#check @QuantumOracle.ConditioningInitialization.J_uniform_eq_pC_empty

-- These actual two-error reductions do not assert a numerical conditioning bound.
#check @QuantumOracle.ConditioningComparison.ordinary_error_le
#check @QuantumOracle.ConditioningComparison.marked_error_le

-- Actual residual removal, adjoints, and capped filtration transfer have no spectral premises.
#check @QuantumOracle.ResidualRemoval.insert_remove
#check @QuantumOracle.ResidualRemoval.size_remove_add_one
#check @QuantumOracle.ResidualRemoval.mem_range_jointInsert_iff
#check @QuantumOracle.ResidualAdjoint.adjoin_mem_K
#check @QuantumOracle.ResidualAdjoint.restrict_mem_orthogonal
#check @QuantumOracle.ResidualKnowledge.restrict_mem_K

-- Two residual degrees and physical support follow from the actual filtration geometry.
#check @QuantumOracle.ResidualLayers.restrict_mem_zero
#check @QuantumOracle.ResidualLayers.restrict_mem_two_layers
#check @QuantumOracle.PolarOrthogonal.candidate_mem_exactLevel_iff
#check @QuantumOracle.ConditioningDegree.J_supported_two_levels
#check @QuantumOracle.ConditioningDegree.JInverse_supported_two_levels
#check @QuantumOracle.ConditioningDegree.D_supported_two_levels

-- Inverse two-error reductions still require a separate numerical conditioning estimate.
#check @QuantumOracle.ConditioningInverseComparison.inverse_ordinary_error_le
#check @QuantumOracle.ConditioningInverseComparison.inverse_marked_error_le

-- Actual degree components and finite-workspace stability.
#print axioms QuantumOracle.CompressionDegree.pC_undefinedPart_mem_succ
#print axioms QuantumOracle.CompressionDegree.project_pC_candidate
#print axioms QuantumOracle.CompressionDegree.project_succ_pC_candidate
#print axioms QuantumOracle.CompressionDegree.candidate_components_inner_eq_zero
#print axioms QuantumOracle.CompressionDegree.pC_candidate_decomposition
#print axioms QuantumOracle.CompressionDegree.candidate_components_norm_sq
#print axioms QuantumOracle.ConditioningError.slice_discrepancy
#print axioms QuantumOracle.ConditioningError.error_sq_eq_sum_slices
#print axioms QuantumOracle.ConditioningError.error_le_of_slice_bounds
#print axioms QuantumOracle.ConditioningError.error_le_of_supported
#print axioms QuantumOracle.ConditioningError.error_le_of_supported_K
#check @QuantumOracle.ConditioningError.error_le_of_supported_K

-- These actual tail overlaps retain the genuine Gram eigenvector equations.
#print axioms QuantumOracle.ConditioningSpectrum.candidate_apply_insert_of_gram_eigen
#print axioms QuantumOracle.ConditioningSpectrum.J_apply_insert_of_gram_eigen
#print axioms QuantumOracle.ConditioningSpectrum.candidate_apply_insert_eq_ratio_J
#print axioms QuantumOracle.ConditioningSpectrum.definedPart_candidate_eq_ratio_J
#print axioms QuantumOracle.ConditioningSpectrum.J_mem_exactLevel
#print axioms QuantumOracle.ConditioningSpectrum.inner_J_pC_candidate
#print axioms QuantumOracle.ConditioningSpectrum.norm_pC_candidate_sub_J_sq
#print axioms QuantumOracle.ConditioningSpectrum.sqrt_ratio_pos_le_one
#print axioms QuantumOracle.ConditioningSpectrum.residual_eigenvalue_le
#check @QuantumOracle.ConditioningSpectrum.inner_J_pC_candidate
#check @QuantumOracle.ConditioningSpectrum.norm_pC_candidate_sub_J_sq

-- The adapted Apache-2.0 ProofAtlas source is checked in the local toolchain.
#print axioms QuantumOracle.HookLengthCompat.coeff_eq_sum
#print axioms AtlasKnownTheorems.HookLengthFormula.standardTableauxErasedSigmaEquiv
#print axioms AtlasKnownTheorems.HookLengthFormula.standardTableauCount_eq_sum_erased
#print axioms AtlasKnownTheorems.HookLengthFormula.hookProductBranchingIdentity_of_content
#print axioms AtlasKnownTheorems.HookLengthFormula.hookLengthFormula
#check @AtlasKnownTheorems.HookLengthFormula.hookLengthFormula
#print AtlasKnownTheorems.HookLengthFormula.HookLengthFormulaStatement

-- Genuine tableau count ratios: no Specht dimension or eigenvalue assertion.
#print axioms QuantumOracle.YoungHookRatio.standardTableauCount_pos
#print axioms QuantumOracle.YoungHookRatio.standardTableauCount_eq_factorial_div_hookProduct
#print axioms QuantumOracle.YoungHookRatio.corner_count_mul_hookProduct
#print axioms QuantumOracle.YoungHookRatio.corner_count_ratio
#print axioms QuantumOracle.YoungHookRatio.corner_count_ratio_real
#print axioms QuantumOracle.YoungHookRatio.cornerWeight_pos
#print axioms QuantumOracle.YoungHookRatio.cornerWeight_eq_hook_ratio
#print axioms QuantumOracle.YoungHookRatio.sum_cornerWeight
#print axioms QuantumOracle.YoungHookRatio.cornerWeight_le_one
#print axioms QuantumOracle.YoungHookRatio.hook_ratio_mem_Ioc
#check @QuantumOracle.YoungHookRatio.corner_count_ratio_real
#check @QuantumOracle.YoungHookRatio.sum_cornerWeight

-- Actual equal-degree residual overlap, under explicit Gram eigenvector equations.
#print axioms QuantumOracle.ConditioningFirstRow.raw_apply_eq_zero_of_defined
#print axioms QuantumOracle.ConditioningFirstRow.definedPart_raw_eq_zero
#print axioms QuantumOracle.ConditioningFirstRow.definedPart_candidate_eq_zero
#print axioms QuantumOracle.ConditioningFirstRow.J_apply_extension_of_gram_eigen
#print axioms QuantumOracle.ConditioningFirstRow.pC_J_apply_base_of_gram_eigen
#print axioms QuantumOracle.ConditioningFirstRow.pC_J_apply_base_eq_ratio_candidate
#print axioms QuantumOracle.ConditioningFirstRow.inner_J_pC_candidate
#print axioms QuantumOracle.ConditioningFirstRowBounds.norm_pC_candidate_sub_J_sq
#print axioms QuantumOracle.ConditioningFirstRowBounds.sqrt_ratio_pos_le_one
#print axioms QuantumOracle.ConditioningFirstRowBounds.full_eigenvalue_le
#check @QuantumOracle.ConditioningFirstRow.definedPart_candidate_eq_zero
#check @QuantumOracle.ConditioningFirstRow.inner_J_pC_candidate
#check @QuantumOracle.ConditioningFirstRowBounds.norm_pC_candidate_sub_J_sq
#check @QuantumOracle.ConditioningFirstRowBounds.sqrt_ratio_pos_le_one
#check @QuantumOracle.ConditioningFirstRowBounds.full_eigenvalue_le

/-!
Standalone audit of actual Specht foundations. The typed checks pin the full
hypothesis scope, while the axiom prints inspect both constructed objects and
theorems. This audit makes no assertion about QuantumOracle Gram eigenspaces.
-/

open QuantumOracle.SpechtFoundation
open scoped BigOperators Classical

#check (specht_simple : ∀ (N : ℕ) (la : Nat.Partition N),
  IsSimpleModule (GroupAlgebra N) (specht N la))

#check (specht_eq_span : ∀ (N : ℕ) (la : Nat.Partition N),
  specht N la = Submodule.span (GroupAlgebra N) {youngSymmetrizer N la})

#check (dimension_eq_tableauCount : ∀ (N : ℕ) (la : Nat.Partition N),
  Module.finrank ℂ (specht N la) = tableauCount N la)

#check (tableauCount_mul_hookProduct : ∀ (N : ℕ) (la : Nat.Partition N),
  tableauCount N la * hookProduct (diagram la) = N.factorial)

#check (dimension_eq_factorial_div_hookProduct : ∀ (N : ℕ) (la : Nat.Partition N),
  Module.finrank ℂ (specht N la) = N.factorial / hookProduct (diagram la))

#check (dimension_mul_hookProduct : ∀ (N : ℕ) (la : Nat.Partition N),
  Module.finrank ℂ (specht N la) * hookProduct (diagram la) = N.factorial)

#check (action_apply_val : ∀ (N : ℕ) (la : Nat.Partition N)
    (sigma : Equiv.Perm (Fin N)) (v : specht N la),
  (action N la sigma v).val = MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) sigma * v.val)

#check (character_eq_trace : ∀ (N : ℕ) (la : Nat.Partition N) (sigma : Equiv.Perm (Fin N)),
  character N la sigma = LinearMap.trace ℂ (specht N la) (action N la sigma))

#check (character_restrict : ∀ (N : ℕ) (mu : Nat.Partition (N + 1))
    (sigma : Equiv.Perm (Fin N)),
  character (N + 1) mu (includePerm N sigma) =
    ∑ la ∈ removeCorners mu, character N la sigma)

#check (branching_multiplicity : ∀ (N : ℕ) (la : Nat.Partition N) (mu : Nat.Partition (N + 1)),
  characterPairing N (character N la)
      (fun sigma => character (N + 1) mu (includePerm N sigma)) =
    if diagram la ≤ diagram mu then 1 else 0)

#check (QuantumOracle.SpechtHookBridge.tableauCount_eq_proofAtlas :
  ∀ (N : ℕ) (la : Nat.Partition N), tableauCount N la =
    AtlasKnownTheorems.HookLengthFormula.standardTableauCount (diagram la))

#check (QuantumOracle.SpechtHookBridge.dimension_eq_proofAtlas_tableauCount :
  ∀ (N : ℕ) (la : Nat.Partition N), Module.finrank ℂ (specht N la) =
    AtlasKnownTheorems.HookLengthFormula.standardTableauCount (diagram la))

#print axioms QuantumOracle.SpechtFoundation.GroupAlgebra
#print axioms QuantumOracle.SpechtFoundation.rowSymmetrizer
#print axioms QuantumOracle.SpechtFoundation.columnAntisymmetrizer
#print axioms QuantumOracle.SpechtFoundation.youngSymmetrizer
#print axioms QuantumOracle.SpechtFoundation.specht
#print axioms QuantumOracle.SpechtFoundation.StandardTableau
#print axioms QuantumOracle.SpechtFoundation.tableauCount
#print axioms QuantumOracle.SpechtFoundation.hookProduct
#print axioms QuantumOracle.SpechtFoundation.action
#print axioms QuantumOracle.SpechtFoundation.representation
#print axioms QuantumOracle.SpechtFoundation.character
#print axioms QuantumOracle.SpechtFoundation.includePerm
#print axioms QuantumOracle.SpechtFoundation.removeCorners
#print axioms QuantumOracle.SpechtFoundation.characterPairing
#print axioms QuantumOracle.SpechtFoundation.youngSymmetrizer_eq
#print axioms QuantumOracle.SpechtFoundation.specht_eq_span
#print axioms QuantumOracle.SpechtFoundation.specht_simple
#print axioms QuantumOracle.SpechtFoundation.hookLength_eq
#print axioms QuantumOracle.SpechtFoundation.hookProduct_eq_prod
#print axioms QuantumOracle.SpechtFoundation.hookProduct_pos
#print axioms QuantumOracle.SpechtFoundation.dimension_eq_tableauCount
#print axioms QuantumOracle.SpechtFoundation.tableauCount_mul_hookProduct
#print axioms QuantumOracle.SpechtFoundation.hookProduct_dvd_factorial
#print axioms QuantumOracle.SpechtFoundation.dimension_eq_factorial_div_hookProduct
#print axioms QuantumOracle.SpechtFoundation.dimension_mul_hookProduct
#print axioms QuantumOracle.SpechtFoundation.action_apply_val
#print axioms QuantumOracle.SpechtFoundation.representation_apply
#print axioms QuantumOracle.SpechtFoundation.character_eq_trace
#print axioms QuantumOracle.SpechtFoundation.includePerm_eq
#print axioms QuantumOracle.SpechtFoundation.mem_removeCorners
#print axioms QuantumOracle.SpechtFoundation.character_restrict
#print axioms QuantumOracle.SpechtFoundation.characterPairing_eq_sum
#print axioms QuantumOracle.SpechtFoundation.branching_multiplicity
#print axioms QuantumOracle.SpechtHookBridge.hookLength_eq_proofAtlas
#print axioms QuantumOracle.SpechtHookBridge.hookProduct_eq_proofAtlas
#print axioms QuantumOracle.SpechtHookBridge.diagram_card
#print axioms QuantumOracle.SpechtHookBridge.tableauCount_eq_proofAtlas
#print axioms QuantumOracle.SpechtHookBridge.dimension_eq_proofAtlas_tableauCount


-- Actual coefficient transport and central Gram convolution, without spectral premises.
#print axioms QuantumOracle.GramConvolution.equiv
#print axioms QuantumOracle.GramConvolution.equiv_coeff
#print axioms QuantumOracle.GramConvolution.equiv_single
#print axioms QuantumOracle.GramConvolution.equiv_relabel_left
#print axioms QuantumOracle.GramConvolution.equiv_relabel_right
#print axioms QuantumOracle.GramConvolution.kernel
#print axioms QuantumOracle.GramConvolution.kernel_coeff
#print axioms QuantumOracle.GramConvolution.sum_coeff_basis
#print axioms QuantumOracle.GramConvolution.equiv_gram
#print axioms QuantumOracle.GramConvolution.kernel_commutes_basis
#print axioms QuantumOracle.GramConvolution.kernel_commutes
#print axioms QuantumOracle.GramConvolution.kernel_mem_center
#print axioms QuantumOracle.GramConvolution.equiv_gram_left
#print axioms QuantumOracle.GramConvolution.gram_mem_leftIdeal
#check @QuantumOracle.GramConvolution.equiv_gram
#check @QuantumOracle.GramConvolution.gram_mem_leftIdeal

-- Scalarity of the actual Gram restriction to the constructed Specht ideal.
#print axioms QuantumOracle.SpechtGram.space
#print axioms QuantumOracle.SpechtGram.mem_space
#print axioms QuantumOracle.SpechtGram.gram_mem
#print axioms QuantumOracle.SpechtGram.restrictedGram
#print axioms QuantumOracle.SpechtGram.restrictedGram_apply_val
#print axioms QuantumOracle.SpechtGram.algebraGram
#print axioms QuantumOracle.SpechtGram.algebraGram_apply_val
#print axioms QuantumOracle.SpechtGram.algebraGram_scalar
#print axioms QuantumOracle.SpechtGram.gram_scalar
#print axioms QuantumOracle.SpechtGram.restrictedGram_scalar
#check @QuantumOracle.SpechtGram.gram_mem
#check @QuantumOracle.SpechtGram.gram_scalar
#check @QuantumOracle.SpechtGram.restrictedGram_scalar

-- The actual scalar is a finite trace-character sum, without supplied eigenvalue premises.
#print axioms QuantumOracle.SpechtCharacter.kernel_eq_sum
#print axioms QuantumOracle.SpechtCharacter.algebraGram_eq_sum_action
#print axioms QuantumOracle.SpechtCharacter.trace_algebraGram
#print axioms QuantumOracle.SpechtCharacter.dimension_ne_zero
#print axioms QuantumOracle.SpechtCharacter.eigenvalue
#print axioms QuantumOracle.SpechtCharacter.scalar_eq_eigenvalue
#print axioms QuantumOracle.SpechtCharacter.gram_eq_eigenvalue
#print axioms QuantumOracle.SpechtCharacter.eigenvalue_eq_fixedPoint_character_sum
#check @QuantumOracle.SpechtCharacter.gram_eq_eigenvalue
#check @QuantumOracle.SpechtCharacter.eigenvalue_eq_fixedPoint_character_sum

-- Actual parallel proof track: SpechtMultiplicity.
#print axioms QuantumOracle.SpechtMultiplicity.Tuple
#print axioms QuantumOracle.SpechtMultiplicity.tuplePerm
#print axioms QuantumOracle.SpechtMultiplicity.tuplePerm_apply
#print axioms QuantumOracle.SpechtMultiplicity.tupleRepresentation
#print axioms QuantumOracle.SpechtMultiplicity.tupleRepresentation_apply
#print axioms QuantumOracle.SpechtMultiplicity.fixedTupleEquiv
#print axioms QuantumOracle.SpechtMultiplicity.card_fixedTuples
#print axioms QuantumOracle.SpechtMultiplicity.card_fixedPoints_symm
#print axioms QuantumOracle.SpechtMultiplicity.tuple_character
#print axioms QuantumOracle.SpechtMultiplicity.tupleMultiplicity
#print axioms QuantumOracle.SpechtMultiplicity.tupleMultiplicity_eq_character_average
#print axioms QuantumOracle.SpechtMultiplicity.tupleMultiplicity_eq_fixedPoint_average
#print axioms QuantumOracle.SpechtMultiplicity.kernel_coeff_eq_tuple_character
#print axioms QuantumOracle.SpechtMultiplicity.eigenvalue_eq_choose_mul_multiplicity
#print axioms QuantumOracle.SpechtMultiplicity.gram_eq_choose_mul_multiplicity

-- Actual parallel proof track: SpechtBranchingMultiplicity.
#print axioms QuantumOracle.SpechtBranchingMultiplicity.pointwiseStabilizer
#print axioms QuantumOracle.SpechtBranchingMultiplicity.mem_pointwiseStabilizer
#print axioms QuantumOracle.SpechtBranchingMultiplicity.stabilizerInvariants
#print axioms QuantumOracle.SpechtBranchingMultiplicity.mem_stabilizerInvariants
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleBasis
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleRepresentation_single
#print axioms QuantumOracle.SpechtBranchingMultiplicity.exists_moveTuple
#print axioms QuantumOracle.SpechtBranchingMultiplicity.evaluation
#print axioms QuantumOracle.SpechtBranchingMultiplicity.evaluation_injective
#print axioms QuantumOracle.SpechtBranchingMultiplicity.evaluation_surjective
#print axioms QuantumOracle.SpechtBranchingMultiplicity.evaluationEquiv
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleMultiplicity_eq_stabilizer_finrank
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleMultiplicity_eq_initialStabilizer_finrank
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleMultiplicity_eq_stabilizer_average
#print axioms QuantumOracle.SpechtBranchingMultiplicity.fixedPoint_average_eq_stabilizer_average
#print axioms QuantumOracle.SpechtBranchingMultiplicity.tupleMultiplicity_zero

-- Actual parallel proof track: SpechtLayers.
#print axioms QuantumOracle.SpechtLayers.exists_ne_zero
#print axioms QuantumOracle.SpechtLayers.mem_orthogonal_iff
#print axioms QuantumOracle.SpechtLayers.mem_K_iff
#print axioms QuantumOracle.SpechtLayers.mem_H_zero_iff
#print axioms QuantumOracle.SpechtLayers.mem_H_succ_iff
#print axioms QuantumOracle.SpechtLayers.space_le_K_iff
#print axioms QuantumOracle.SpechtLayers.space_le_orthogonal_iff
#print axioms QuantumOracle.SpechtLayers.space_le_H_zero_iff
#print axioms QuantumOracle.SpechtLayers.space_le_H_succ_iff
#print axioms QuantumOracle.SpechtLayers.eigenvalue_eq_energy_div_norm_sq
#print axioms QuantumOracle.SpechtLayers.eigenvalue_im_eq_zero
#print axioms QuantumOracle.SpechtLayers.eigenvalue_re_nonneg
#print axioms QuantumOracle.SpechtLayers.eigenvalue_eq_ofReal_re
#print axioms QuantumOracle.SpechtLayers.eigenvalue_re_pos_iff
#print axioms QuantumOracle.SpechtLayers.eigenvalue_re_pos_of_mem_K
#print axioms QuantumOracle.SpechtLayers.eigenvalue_ne_zero_mono
#print axioms QuantumOracle.SpechtLayers.eigenvalue_eq_zero_of_gt
#print axioms QuantumOracle.SpechtLayers.eigenvalue_full_ne_zero

-- Actual parallel proof track: HookRatioBounds.
#print axioms QuantumOracle.HookRatioBounds.rowLen_zero_le_card
#print axioms QuantumOracle.HookRatioBounds.sum_colLen
#print axioms QuantumOracle.HookRatioBounds.colLen_pos_of_lt_rowLen
#print axioms QuantumOracle.HookRatioBounds.column_index_lt_card
#print axioms QuantumOracle.HookRatioBounds.firstRowDefect
#print axioms QuantumOracle.HookRatioBounds.firstRowRatioSq
#print axioms QuantumOracle.HookRatioBounds.firstRowDefect_mem_Icc
#print axioms QuantumOracle.HookRatioBounds.firstRowDefect_le
#print axioms QuantumOracle.HookRatioBounds.firstRow_deficit_bound
#print axioms QuantumOracle.HookRatioBounds.tailCornerRatioSq
#print axioms QuantumOracle.HookRatioBounds.corner_column_lt_rowLen
#print axioms QuantumOracle.HookRatioBounds.tailCorner_deficit_bound
#print axioms QuantumOracle.HookRatioBounds.firstRow_deficit_le_two_div
#print axioms QuantumOracle.HookRatioBounds.tailCorner_deficit_le_two_div

-- Actual parallel proof track: HookRatioProducts.
#print axioms QuantumOracle.HookRatioProducts.rowFactor
#print axioms QuantumOracle.HookRatioProducts.normalizedRowProduct
#print axioms QuantumOracle.HookRatioProducts.rowFactor_pos
#print axioms QuantumOracle.HookRatioProducts.normalizedRowProduct_pos
#print axioms QuantumOracle.HookRatioProducts.normalizedRowProduct_firstRow_ratio
#print axioms QuantumOracle.HookRatioProducts.colLen_eq_zero_of_ge
#print axioms QuantumOracle.HookRatioProducts.normalizedRowProduct_eq_prod
#print axioms QuantumOracle.HookRatioProducts.colLen_eraseCorner_of_ne
#print axioms QuantumOracle.HookRatioProducts.colLen_eraseCorner_add_one
#print axioms QuantumOracle.HookRatioProducts.rowLen_eraseCorner_le
#print axioms QuantumOracle.HookRatioProducts.normalizedRowProduct_tailCorner_ratio
#print axioms QuantumOracle.HookRatioProducts.firstRow_quotient_deficit_bound
#print axioms QuantumOracle.HookRatioProducts.tailCorner_quotient_deficit_bound
#print axioms QuantumOracle.HookRatioProducts.firstRow_quotient_deficit_le_two_div
#print axioms QuantumOracle.HookRatioProducts.tailCorner_quotient_deficit_le_two_div

-- Actual parallel proof track: CoherentComparison.
#print axioms QuantumOracle.CoherentComparison.controlSlice
#print axioms QuantumOracle.CoherentComparison.ordinarySlice
#print axioms QuantumOracle.CoherentComparison.norm_sq_eq_controlSlices
#print axioms QuantumOracle.CoherentComparison.norm_sq_eq_ordinarySlices
#print axioms QuantumOracle.CoherentComparison.controlSlice_onOracle
#print axioms QuantumOracle.CoherentComparison.ordinarySlice_onOracle
#print axioms QuantumOracle.CoherentComparison.difference
#print axioms QuantumOracle.CoherentComparison.controlSlice_difference_disabled
#print axioms QuantumOracle.CoherentComparison.controlSlice_difference_marked
#print axioms QuantumOracle.CoherentComparison.ordinarySlice_difference
#print axioms QuantumOracle.CoherentComparison.marked_error_le
#print axioms QuantumOracle.CoherentComparison.ordinary_error_le
#print axioms QuantumOracle.CoherentComparison.auxiliarySlice
#print axioms QuantumOracle.CoherentComparison.norm_sq_eq_auxiliarySlices
#print axioms QuantumOracle.CoherentComparison.auxiliarySlice_onOracle
#print axioms QuantumOracle.CoherentComparison.liftedDifference
#print axioms QuantumOracle.CoherentComparison.auxiliarySlice_liftedDifference
#print axioms QuantumOracle.CoherentComparison.lifted_error_le

-- Actual parallel proof track: ConditioningLocalBound.
#print axioms QuantumOracle.ConditioningLocalBound.Bound
#print axioms QuantumOracle.ConditioningLocalBound.ordinary_supported_succ
#print axioms QuantumOracle.ConditioningLocalBound.marked_supported_succ
#print axioms QuantumOracle.ConditioningLocalBound.inversion_supported
#print axioms QuantumOracle.ConditioningLocalBound.ordinary_forward_error_le
#print axioms QuantumOracle.ConditioningLocalBound.marked_forward_error_le
#print axioms QuantumOracle.ConditioningLocalBound.ordinary_error_le
#print axioms QuantumOracle.ConditioningLocalBound.marked_error_le

-- Actual parallel proof track: ConditioningSoundness.
#print axioms QuantumOracle.ConditioningSoundness.controlSlice_supported
#print axioms QuantumOracle.ConditioningSoundness.ordinarySlice_supported
#print axioms QuantumOracle.ConditioningSoundness.auxiliarySlice_supported
#print axioms QuantumOracle.ConditioningSoundness.query_error_le
#print axioms QuantumOracle.ConditioningSoundness.lifted_query_error_le
#print axioms QuantumOracle.ConditioningSoundness.bound_mono
#print axioms QuantumOracle.ConditioningSoundness.localError_le
#print axioms QuantumOracle.ConditioningSoundness.dist_le_of_conditioning_bound
#print axioms QuantumOracle.ConditioningSoundness.dist_le_four_mul_div_sqrt_of_conditioning_bound

#check @QuantumOracle.SpechtMultiplicity.eigenvalue_eq_choose_mul_multiplicity
#check @QuantumOracle.SpechtBranchingMultiplicity.evaluationEquiv
#check @QuantumOracle.SpechtBranchingMultiplicity.tupleMultiplicity_eq_stabilizer_average
#check @QuantumOracle.SpechtLayers.space_le_H_succ_iff
#check @QuantumOracle.HookRatioProducts.normalizedRowProduct_firstRow_ratio
#check @QuantumOracle.HookRatioProducts.normalizedRowProduct_tailCorner_ratio
#check @QuantumOracle.ConditioningLocalBound.Bound
#check @QuantumOracle.ConditioningSoundness.dist_le_four_mul_div_sqrt_of_conditioning_bound

-- Actual parallel proof track: HookRowFactorization.
#print axioms QuantumOracle.HookRowFactorization.shiftRow
#print axioms QuantumOracle.HookRowFactorization.tail
#print axioms QuantumOracle.HookRowFactorization.mem_tail
#print axioms QuantumOracle.HookRowFactorization.tail_rowLen
#print axioms QuantumOracle.HookRowFactorization.tail_colLen
#print axioms QuantumOracle.HookRowFactorization.tail_rowLen_le
#print axioms QuantumOracle.HookRowFactorization.tail_map_cells
#print axioms QuantumOracle.HookRowFactorization.hookAt
#print axioms QuantumOracle.HookRowFactorization.hookLength_eq_hookAt
#print axioms QuantumOracle.HookRowFactorization.hookProduct_eq_prod_hookAt
#print axioms QuantumOracle.HookRowFactorization.hookAt_shiftRow
#print axioms QuantumOracle.HookRowFactorization.firstRowHookProduct
#print axioms QuantumOracle.HookRowFactorization.hookProduct_factorization
#print axioms QuantumOracle.HookRowFactorization.hookAt_firstRow
#print axioms QuantumOracle.HookRowFactorization.firstRowHookProduct_eq_prod
#print axioms QuantumOracle.HookRowFactorization.prod_range_sub_eq_factorial
#print axioms QuantumOracle.HookRowFactorization.firstRowHookProduct_div_factorial
#print axioms QuantumOracle.HookRowFactorization.hookProduct_div_tail_factorial
#print axioms QuantumOracle.HookRowFactorization.card_eq_firstRow_add_tail
#print axioms QuantumOracle.HookRowFactorization.choose_mul_tableauCount_ratio

-- Actual parallel proof track: ConditioningHookBounds.
#print axioms QuantumOracle.ConditioningHookBounds.firstRow_error_le
#print axioms QuantumOracle.ConditioningHookBounds.tailCorner_error_le

-- Actual parallel proof track: ResidualEquivariance.
#print axioms QuantumOracle.ResidualEquivariance.stabilizerEmbed
#print axioms QuantumOracle.ResidualEquivariance.stabilizerEmbed_at
#print axioms QuantumOracle.ResidualEquivariance.stabilizerEmbed_succAbove
#print axioms QuantumOracle.ResidualEquivariance.stabilizerEmbed_injective
#print axioms QuantumOracle.ResidualEquivariance.mem_range_stabilizerEmbed
#print axioms QuantumOracle.ResidualEquivariance.insert_relabel
#print axioms QuantumOracle.ResidualEquivariance.restrict_relabel
#print axioms QuantumOracle.ResidualEquivariance.restrict_relabel_linearMap

-- Actual parallel proof track: SpechtIsotypic.
#print axioms QuantumOracle.SpechtIsotypic.component
#print axioms QuantumOracle.SpechtIsotypic.space
#print axioms QuantumOracle.SpechtIsotypic.mem_space
#print axioms QuantumOracle.SpechtIsotypic.specht_le_component
#print axioms QuantumOracle.SpechtIsotypic.spechtSpace_le_space
#print axioms QuantumOracle.SpechtIsotypic.algebraGram
#print axioms QuantumOracle.SpechtIsotypic.algebraGram_apply
#print axioms QuantumOracle.SpechtIsotypic.kernel_smul_specht
#print axioms QuantumOracle.SpechtIsotypic.algebraGram_eq_eigenvalue
#print axioms QuantumOracle.SpechtIsotypic.gram_eq_eigenvalue
#print axioms QuantumOracle.SpechtIsotypic.iSup_component_eq_top
#print axioms QuantumOracle.SpechtIsotypic.iSup_space_eq_top

-- Actual parallel proof track: SpechtBranchingPaths.
#print axioms QuantumOracle.SpechtBranchingPaths.snocTuple
#print axioms QuantumOracle.SpechtBranchingPaths.snocTuple_last
#print axioms QuantumOracle.SpechtBranchingPaths.snocTuple_castSucc
#print axioms QuantumOracle.SpechtBranchingPaths.includePerm_last
#print axioms QuantumOracle.SpechtBranchingPaths.includePerm_castSucc
#print axioms QuantumOracle.SpechtBranchingPaths.includePerm_eq_insert
#print axioms QuantumOracle.SpechtBranchingPaths.stabilizerSuccEquiv
#print axioms QuantumOracle.SpechtBranchingPaths.stabilizerSuccEquiv_apply_val
#print axioms QuantumOracle.SpechtBranchingPaths.stabilizer_finrank_snoc
#print axioms QuantumOracle.SpechtBranchingPaths.tupleMultiplicity_succ

-- Actual parallel proof track: SpechtTrivialMultiplicity.
#print axioms QuantumOracle.SpechtTrivialMultiplicity.indiscrete_eq_positivePartition
#print axioms QuantumOracle.SpechtTrivialMultiplicity.action_indiscrete_eq_id
#print axioms QuantumOracle.SpechtTrivialMultiplicity.dimension_indiscrete_pos
#print axioms QuantumOracle.SpechtTrivialMultiplicity.dimension_zero
#print axioms QuantumOracle.SpechtTrivialMultiplicity.character_indiscrete
#print axioms QuantumOracle.SpechtTrivialMultiplicity.tupleMultiplicity_zero_eq_indiscrete
#print axioms QuantumOracle.SpechtTrivialMultiplicity.indiscrete_rowLen_zero
#print axioms QuantumOracle.SpechtTrivialMultiplicity.rowLen_zero_eq_iff_indiscrete
#print axioms QuantumOracle.SpechtTrivialMultiplicity.tupleMultiplicity_zero_eq_indicator
#print axioms QuantumOracle.SpechtTrivialMultiplicity.tupleMultiplicity_zero_of_rowLen_lt

-- Actual parallel proof track: SpechtMultiplicitySupport.
#print axioms QuantumOracle.SpechtMultiplicitySupport.eigenvalue_eq_zero_iff_tupleMultiplicity_eq_zero
#print axioms QuantumOracle.SpechtMultiplicitySupport.tupleMultiplicity_ne_zero_mono
#print axioms QuantumOracle.SpechtMultiplicitySupport.rowLen_le_of_mem_removeCorners
#print axioms QuantumOracle.SpechtMultiplicitySupport.tupleMultiplicity_eq_zero_of_rowLen_lt
#print axioms QuantumOracle.SpechtMultiplicitySupport.eigenvalue_eq_zero_of_rowLen_lt
#print axioms QuantumOracle.SpechtMultiplicitySupport.gram_eq_zero_of_rowLen_lt
#print axioms QuantumOracle.SpechtMultiplicitySupport.tupleMultiplicity_succ_eq_sum_preserving_rowLen

-- Actual parallel proof track: SpechtOrthogonal.
#print axioms QuantumOracle.SpechtOrthogonal.component_ne
#print axioms QuantumOracle.SpechtOrthogonal.component_disjoint
#print axioms QuantumOracle.SpechtOrthogonal.relabel_left_mem
#print axioms QuantumOracle.SpechtOrthogonal.map_space_relabel_left
#print axioms QuantumOracle.SpechtOrthogonal.projection_relabel_left
#print axioms QuantumOracle.SpechtOrthogonal.projectionLinear
#print axioms QuantumOracle.SpechtOrthogonal.projectionLinear_apply
#print axioms QuantumOracle.SpechtOrthogonal.projectionLinear_mul_basis
#print axioms QuantumOracle.SpechtOrthogonal.projectionAlgebra
#print axioms QuantumOracle.SpechtOrthogonal.projectionAlgebra_apply
#print axioms QuantumOracle.SpechtOrthogonal.projection_mem_space
#print axioms QuantumOracle.SpechtOrthogonal.projection_eq_zero_of_ne
#print axioms QuantumOracle.SpechtOrthogonal.space_le_orthogonal
#print axioms QuantumOracle.SpechtOrthogonal.inner_eq_zero
#print axioms QuantumOracle.SpechtOrthogonal.orthogonalFamily
#print axioms QuantumOracle.SpechtOrthogonal.sum_projection

-- Actual parallel proof track: SpechtIsotypicLayers.
#print axioms QuantumOracle.SpechtIsotypicLayers.exists_ne_zero
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_orthogonal_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_K_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_H_zero_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_H_succ_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.space_le_K_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.space_le_orthogonal_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.space_le_H_zero_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.space_le_H_succ_iff
#print axioms QuantumOracle.SpechtIsotypicLayers.eigenvalue_eq_energy_div_norm_sq
#print axioms QuantumOracle.SpechtIsotypicLayers.eigenvalue_re_pos_of_mem_K
#print axioms QuantumOracle.SpechtIsotypicLayers.projection_gram
#print axioms QuantumOracle.SpechtIsotypicLayers.projection_mem_K
#print axioms QuantumOracle.SpechtIsotypicLayers.projection_mem_orthogonal
#print axioms QuantumOracle.SpechtIsotypicLayers.projection_mem_H
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_K_iff_projection_eq_zero
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_orthogonal_iff_projection_eq_zero
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_H_zero_iff_projection_eq_zero
#print axioms QuantumOracle.SpechtIsotypicLayers.mem_H_succ_iff_projection_support
#print axioms QuantumOracle.SpechtIsotypicLayers.K_eq_iSup
#print axioms QuantumOracle.SpechtIsotypicLayers.H_succ_eq_iSup
#print axioms QuantumOracle.SpechtIsotypicLayers.norm_sq_eq_sum_projections

-- Actual parallel proof track: TailBranching.
#print axioms QuantumOracle.TailBranching.diagram_injective
#print axioms QuantumOracle.TailBranching.tail_corner_shift
#print axioms QuantumOracle.TailBranching.removeTailCorner
#print axioms QuantumOracle.TailBranching.removeTailCorner_cells
#print axioms QuantumOracle.TailBranching.removeTailCorner_mem
#print axioms QuantumOracle.TailBranching.removeTailCorner_rowLen
#print axioms QuantumOracle.TailBranching.tail_removeTailCorner
#print axioms QuantumOracle.TailBranching.removeTailCorner_injective
#print axioms QuantumOracle.TailBranching.exists_erased_corner
#print axioms QuantumOracle.TailBranching.removeTailCorner_surjective
#print axioms QuantumOracle.TailBranching.sum_preserving_firstRow

-- Actual parallel proof track: SpechtMinimalMultiplicity.
#print axioms QuantumOracle.SpechtMinimalMultiplicity.rowLen_add_tail_card
#print axioms QuantumOracle.SpechtMinimalMultiplicity.tail_card_le
#print axioms QuantumOracle.SpechtMinimalMultiplicity.tail_eq_bot_of_card_zero
#print axioms QuantumOracle.SpechtMinimalMultiplicity.tupleMultiplicity_minimal_of_tail_empty
#print axioms QuantumOracle.SpechtMinimalMultiplicity.tupleMultiplicity_minimal
#print axioms QuantumOracle.SpechtMinimalMultiplicity.eigenvalue_minimal
#print axioms QuantumOracle.SpechtMinimalMultiplicity.eigenvalue_minimal_re_pos
#print axioms QuantumOracle.SpechtMinimalMultiplicity.eigenvalue_minimal_ne_zero
#print axioms QuantumOracle.SpechtMinimalMultiplicity.tupleMultiplicity_ne_zero_iff_tail_card_le
#print axioms QuantumOracle.SpechtMinimalMultiplicity.eigenvalue_ne_zero_iff_rowLen
#print axioms QuantumOracle.SpechtMinimalMultiplicity.space_le_K_iff_rowLen
#print axioms QuantumOracle.SpechtMinimalMultiplicity.space_le_H_minimal

-- Actual parallel proof track: YoungBranchCases.
#print axioms QuantumOracle.YoungBranchCases.tail_eq_of_erase_firstRow
#print axioms QuantumOracle.YoungBranchCases.rowLen_eq_of_erase_below
#print axioms QuantumOracle.YoungBranchCases.branching_cases
#print axioms QuantumOracle.YoungBranchCases.firstRow_case_of_ne
#print axioms QuantumOracle.YoungBranchCases.tail_case_of_eq
#print axioms QuantumOracle.YoungBranchCases.firstRow_product_ratio
#print axioms QuantumOracle.YoungBranchCases.tail_product_ratio
#print axioms QuantumOracle.YoungBranchCases.branchRatio
#print axioms QuantumOracle.YoungBranchCases.branchRatio_pos
#print axioms QuantumOracle.YoungBranchCases.branchRatio_deficit_le_two_div

-- Actual parallel proof track: SpechtSpectralFormula.
#print axioms QuantumOracle.SpechtSpectralFormula.space_le_K_iff_rowLen
#print axioms QuantumOracle.SpechtSpectralFormula.space_le_H_minimal
#print axioms QuantumOracle.SpechtSpectralFormula.gram_minimal
#print axioms QuantumOracle.SpechtSpectralFormula.space_le_H_iff_tail_card
#print axioms QuantumOracle.SpechtSpectralFormula.space_le_H_orthogonal_of_tail_ne
#print axioms QuantumOracle.SpechtSpectralFormula.mem_H_iff_projection_eq_zero

-- Actual parallel proof track: ResidualSpectralDecomposition.
#print axioms QuantumOracle.ResidualSpectralDecomposition.space
#print axioms QuantumOracle.ResidualSpectralDecomposition.mem_space
#print axioms QuantumOracle.ResidualSpectralDecomposition.project
#print axioms QuantumOracle.ResidualSpectralDecomposition.restrict_project
#print axioms QuantumOracle.ResidualSpectralDecomposition.project_mem
#print axioms QuantumOracle.ResidualSpectralDecomposition.restrict_ext
#print axioms QuantumOracle.ResidualSpectralDecomposition.project_eq_self
#print axioms QuantumOracle.ResidualSpectralDecomposition.inner_eq_sum_restrict
#print axioms QuantumOracle.ResidualSpectralDecomposition.inner_eq_zero
#print axioms QuantumOracle.ResidualSpectralDecomposition.sum_project
#print axioms QuantumOracle.ResidualSpectralDecomposition.residual_gram_project

-- Actual parallel proof track: ResidualSpectralSymmetry.
#print axioms QuantumOracle.ResidualSpectralSymmetry.insert_mul
#print axioms QuantumOracle.ResidualSpectralSymmetry.outputResidual
#print axioms QuantumOracle.ResidualSpectralSymmetry.outputResidual_insert
#print axioms QuantumOracle.ResidualSpectralSymmetry.restrict_relabel_left
#print axioms QuantumOracle.ResidualSpectralSymmetry.project_relabel_left
#print axioms QuantumOracle.ResidualSpectralSymmetry.projectionLinear
#print axioms QuantumOracle.ResidualSpectralSymmetry.projectionLinear_apply
#print axioms QuantumOracle.ResidualSpectralSymmetry.projectionLinear_mul_basis
#print axioms QuantumOracle.ResidualSpectralSymmetry.projectionAlgebra
#print axioms QuantumOracle.ResidualSpectralSymmetry.project_mem_full_space

-- Actual parallel proof track: JointSpectralDecomposition.
#print axioms QuantumOracle.JointSpectralDecomposition.Labels
#print axioms QuantumOracle.JointSpectralDecomposition.space
#print axioms QuantumOracle.JointSpectralDecomposition.project
#print axioms QuantumOracle.JointSpectralDecomposition.project_mem
#print axioms QuantumOracle.JointSpectralDecomposition.inner_eq_zero
#print axioms QuantumOracle.JointSpectralDecomposition.sum_project
#print axioms QuantumOracle.JointSpectralDecomposition.full_gram_project
#print axioms QuantumOracle.JointSpectralDecomposition.residual_gram_project
#print axioms QuantumOracle.JointSpectralDecomposition.orthogonalFamily
#print axioms QuantumOracle.JointSpectralDecomposition.norm_sq_eq_sum_project

-- Actual parallel proof track: ConditioningSpechtBounds.
#print axioms QuantumOracle.ConditioningSpechtBounds.error_le
#print axioms QuantumOracle.ConditioningSpechtBounds.error_project_le

#check @QuantumOracle.SpechtMinimalMultiplicity.tupleMultiplicity_minimal
#check @QuantumOracle.SpechtSpectralFormula.gram_minimal
#check @QuantumOracle.SpechtSpectralFormula.space_le_H_iff_tail_card
#check @QuantumOracle.JointSpectralDecomposition.sum_project
#check @QuantumOracle.JointSpectralDecomposition.norm_sq_eq_sum_project
#check @QuantumOracle.ConditioningSpechtBounds.error_le

-- Actual parallel proof track: SpechtRestrictionHom.
#print axioms QuantumOracle.SpechtRestrictionHom.restricted
#print axioms QuantumOracle.SpechtRestrictionHom.Hom
#print axioms QuantumOracle.SpechtRestrictionHom.finrank_eq_indicator
#print axioms QuantumOracle.SpechtRestrictionHom.finrank_eq_zero_of_not_mem
#print axioms QuantumOracle.SpechtRestrictionHom.hom_eq_zero_of_not_mem
#print axioms QuantumOracle.SpechtRestrictionHom.mem_removeCorners_of_ne_zero
#print axioms QuantumOracle.SpechtRestrictionHom.exists_ne_zero_iff_mem

-- Actual parallel proof track: SpechtRestrictionHomReverse.
#print axioms QuantumOracle.SpechtRestrictionHomReverse.Hom
#print axioms QuantumOracle.SpechtRestrictionHomReverse.finrank_eq_indicator
#print axioms QuantumOracle.SpechtRestrictionHomReverse.finrank_eq_zero_of_not_mem
#print axioms QuantumOracle.SpechtRestrictionHomReverse.hom_eq_zero_of_not_mem
#print axioms QuantumOracle.SpechtRestrictionHomReverse.mem_removeCorners_of_ne_zero
#print axioms QuantumOracle.SpechtRestrictionHomReverse.exists_ne_zero_iff_mem

-- Actual parallel proof track: ConditioningJointBound.
#print axioms QuantumOracle.ConditioningJointBound.error
#print axioms QuantumOracle.ConditioningJointBound.error_apply
#print axioms QuantumOracle.ConditioningJointBound.project_eq_zero_of_tail_gt
#print axioms QuantumOracle.ConditioningJointBound.bound_of_support_and_error_orthogonality

-- Actual parallel proof track: ConditioningCrossTerms.
#print axioms QuantumOracle.ConditioningCrossTerms.inner_pC_swap
#print axioms QuantumOracle.ConditioningCrossTerms.inner_raw_raw
#print axioms QuantumOracle.ConditioningCrossTerms.pC_J_apply_defined_of_size_ne
#print axioms QuantumOracle.ConditioningCrossTerms.project_pC_J_eq_raw
#print axioms QuantumOracle.ConditioningCrossTerms.inner_J_pC_candidate_lower
#print axioms QuantumOracle.ConditioningCrossTerms.inner_J_pC_candidate_tail
#print axioms QuantumOracle.ConditioningCrossTerms.inner_J_pC_candidate_eq_zero
#print axioms QuantumOracle.ConditioningCrossTerms.branch_degrees
#print axioms QuantumOracle.ConditioningCrossTerms.inner_J_pC_candidate_joint_eq_zero
#print axioms QuantumOracle.ConditioningCrossTerms.error_inner_eq_zero

-- Actual parallel proof track: ResidualBranchSupport.
#print axioms QuantumOracle.ResidualBranchSupport.component_equiv_copies
#print axioms QuantumOracle.ResidualBranchSupport.component_map_eq_zero_of_not_mem
#print axioms QuantumOracle.ResidualBranchSupport.projectRestrict
#print axioms QuantumOracle.ResidualBranchSupport.projectRestrict_stabilizer
#print axioms QuantumOracle.ResidualBranchSupport.stabilizerEmbed_last
#print axioms QuantumOracle.ResidualBranchSupport.projectRestrict_last_eq_zero_of_not_mem
#print axioms QuantumOracle.ResidualBranchSupport.restrict_move_answer
#print axioms QuantumOracle.ResidualBranchSupport.projectRestrict_eq_zero_of_not_mem
#print axioms QuantumOracle.ResidualBranchSupport.joint_eq_zero_of_not_mem
#print axioms QuantumOracle.ResidualBranchSupport.mem_removeCorners_of_joint_ne_zero
#print axioms QuantumOracle.ResidualBranchSupport.joint_project_eq_zero_of_not_mem
#print axioms QuantumOracle.ResidualBranchSupport.joint_space_eq_bot_of_not_mem

-- Actual parallel proof track: FiniteSoundness.
#print axioms QuantumOracle.FiniteSoundness.conditioning_bound
#print axioms QuantumOracle.FiniteSoundness.dist_le_four_mul_div_sqrt_succ
#print axioms QuantumOracle.FiniteSoundness.dist_le_four_mul_div_sqrt
#print axioms QuantumOracle.FiniteSoundness.retained_dist_le_four_mul_div_sqrt
#print axioms QuantumOracle.FiniteSoundness.algorithm_distance_le_four_mul_div_sqrt

#check @QuantumOracle.FiniteSoundness.conditioning_bound
#check @QuantumOracle.FiniteSoundness.dist_le_four_mul_div_sqrt
#check @QuantumOracle.FiniteSoundness.retained_dist_le_four_mul_div_sqrt
#check @QuantumOracle.FiniteSoundness.algorithm_distance_le_four_mul_div_sqrt

-- Explicit finite soundness witnesses.
#print axioms QuantumOracle.FiniteSoundnessWitness.local_error_le_four_div_sqrt
#print axioms QuantumOracle.FiniteSoundnessWitness.vector_error_le_four_mul_div_sqrt
#print axioms QuantumOracle.FiniteSoundnessWitness.retainedPurification
#print axioms QuantumOracle.FiniteSoundnessWitness.retainedPurification_distance
#print axioms QuantumOracle.FiniteSoundnessWitness.retainedPurification_distance_le
#print axioms QuantumOracle.FiniteSoundnessWitness.outputPurification
#print axioms QuantumOracle.FiniteSoundnessWitness.outputPurification_distance
#print axioms QuantumOracle.FiniteSoundnessWitness.outputPurification_distance_le
#print axioms QuantumOracle.FiniteSoundnessWitness.exists_retained_purification
#print axioms QuantumOracle.FiniteSoundnessWitness.exists_output_purification

#check @QuantumOracle.FiniteSoundnessWitness.exists_output_purification
#check @QuantumOracle.FiniteSoundnessWitness.vector_error_le_four_mul_div_sqrt

-- Manuscript final-projector clause: ProjectorPurification.
#print axioms QuantumOracle.ProjectorPurification.column
#print axioms QuantumOracle.ProjectorPurification.project
#print axioms QuantumOracle.ProjectorPurification.project_apply
#print axioms QuantumOracle.ProjectorPurification.column_project
#print axioms QuantumOracle.ProjectorPurification.norm_sq_eq_sum_columns
#print axioms QuantumOracle.ProjectorPurification.norm_project_le
#print axioms QuantumOracle.ProjectorPurification.norm_project_sub_le
#print axioms QuantumOracle.ProjectorPurification.abs_project_norm_sub_le_norm
#print axioms QuantumOracle.ProjectorPurification.norm_onWorkspace_eq_of_reduced_eq
#print axioms QuantumOracle.ProjectorPurification.norm_project_eq_of_reduced_eq
#print axioms QuantumOracle.ProjectorPurification.abs_project_norm_sub_le_witness
#print axioms QuantumOracle.ProjectorPurification.abs_project_norm_sub_le_purificationDistance
#print axioms QuantumOracle.ProjectorPurification.abs_project_norm_sub_le_purificationDistance_of_reduced_eq

-- Manuscript final-projector clause: ImprovedSoundness.
#print axioms QuantumOracle.ImprovedSoundness.projected_norm_difference_le_dist
#print axioms QuantumOracle.ImprovedSoundness.projected_norm_difference_le_dist_le_four_mul_div_sqrt
#print axioms QuantumOracle.ImprovedSoundness.soundness

#check @QuantumOracle.ProjectorPurification.abs_project_norm_sub_le_purificationDistance
#check @QuantumOracle.ImprovedSoundness.soundness

-- Canonical specification and its public proof endpoint.
#print axioms QuantumOracle.SoundnessStatement
#print axioms QuantumOracle.soundness
#check QuantumOracle.SoundnessStatement
#check QuantumOracle.soundness
