result_type.vo result_type.glob result_type.v.beautified result_type.required_vo: result_type.v 
result_type.vio: result_type.v 
result_type.vos result_type.vok result_type.required_vos: result_type.v 
primitives.vo primitives.glob primitives.v.beautified primitives.required_vo: primitives.v 
primitives.vio: primitives.v 
primitives.vos primitives.vok primitives.required_vos: primitives.v 
ids.vo ids.glob ids.v.beautified ids.required_vo: ids.v 
ids.vio: ids.v 
ids.vos ids.vok ids.required_vos: ids.v 
kernel_syntax.vo kernel_syntax.glob kernel_syntax.v.beautified kernel_syntax.required_vo: kernel_syntax.v ids.vo primitives.vo
kernel_syntax.vio: kernel_syntax.v ids.vio primitives.vio
kernel_syntax.vos kernel_syntax.vok kernel_syntax.required_vos: kernel_syntax.v ids.vos primitives.vos
type_env.vo type_env.glob type_env.v.beautified type_env.required_vo: type_env.v ids.vo primitives.vo kernel_syntax.vo
type_env.vio: type_env.v ids.vio primitives.vio kernel_syntax.vio
type_env.vos type_env.vok type_env.required_vos: type_env.v ids.vos primitives.vos kernel_syntax.vos
env.vo env.glob env.v.beautified env.required_vo: env.v 
env.vio: env.v 
env.vos env.vok env.required_vos: env.v 
surface_syntax.vo surface_syntax.glob surface_syntax.v.beautified surface_syntax.required_vo: surface_syntax.v ids.vo primitives.vo
surface_syntax.vio: surface_syntax.v ids.vio primitives.vio
surface_syntax.vos surface_syntax.vok surface_syntax.required_vos: surface_syntax.v ids.vos primitives.vos
values.vo values.glob values.v.beautified values.required_vo: values.v ids.vo primitives.vo kernel_syntax.vo env.vo type_theory.vo pattern_theory.vo elaboration.vo
values.vio: values.v ids.vio primitives.vio kernel_syntax.vio env.vio type_theory.vio pattern_theory.vio elaboration.vio
values.vos values.vok values.required_vos: values.v ids.vos primitives.vos kernel_syntax.vos env.vos type_theory.vos pattern_theory.vos elaboration.vos
desugarer.vo desugarer.glob desugarer.v.beautified desugarer.required_vo: desugarer.v primitives.vo ids.vo kernel_syntax.vo surface_syntax.vo
desugarer.vio: desugarer.v primitives.vio ids.vio kernel_syntax.vio surface_syntax.vio
desugarer.vos desugarer.vok desugarer.required_vos: desugarer.v primitives.vos ids.vos kernel_syntax.vos surface_syntax.vos
programs.vo programs.glob programs.v.beautified programs.required_vo: programs.v result_type.vo ids.vo primitives.vo env.vo values.vo surface_syntax.vo kernel_syntax.vo desugarer.vo elaboration.vo evaluation.vo
programs.vio: programs.v result_type.vio ids.vio primitives.vio env.vio values.vio surface_syntax.vio kernel_syntax.vio desugarer.vio elaboration.vio evaluation.vio
programs.vos programs.vok programs.required_vos: programs.v result_type.vos ids.vos primitives.vos env.vos values.vos surface_syntax.vos kernel_syntax.vos desugarer.vos elaboration.vos evaluation.vos
type_theory.vo type_theory.glob type_theory.v.beautified type_theory.required_vo: type_theory.v ids.vo primitives.vo kernel_syntax.vo type_env.vo env.vo
type_theory.vio: type_theory.v ids.vio primitives.vio kernel_syntax.vio type_env.vio env.vio
type_theory.vos type_theory.vok type_theory.required_vos: type_theory.v ids.vos primitives.vos kernel_syntax.vos type_env.vos env.vos
pattern_theory.vo pattern_theory.glob pattern_theory.v.beautified pattern_theory.required_vo: pattern_theory.v ids.vo primitives.vo kernel_syntax.vo type_env.vo env.vo type_theory.vo
pattern_theory.vio: pattern_theory.v ids.vio primitives.vio kernel_syntax.vio type_env.vio env.vio type_theory.vio
pattern_theory.vos pattern_theory.vok pattern_theory.required_vos: pattern_theory.v ids.vos primitives.vos kernel_syntax.vos type_env.vos env.vos type_theory.vos
elaboration.vo elaboration.glob elaboration.v.beautified elaboration.required_vo: elaboration.v result_type.vo ids.vo primitives.vo kernel_syntax.vo type_env.vo env.vo type_theory.vo pattern_theory.vo
elaboration.vio: elaboration.v result_type.vio ids.vio primitives.vio kernel_syntax.vio type_env.vio env.vio type_theory.vio pattern_theory.vio
elaboration.vos elaboration.vok elaboration.required_vos: elaboration.v result_type.vos ids.vos primitives.vos kernel_syntax.vos type_env.vos env.vos type_theory.vos pattern_theory.vos
evaluation.vo evaluation.glob evaluation.v.beautified evaluation.required_vo: evaluation.v ids.vo primitives.vo result_type.vo env.vo kernel_syntax.vo type_theory.vo elaboration.vo values.vo
evaluation.vio: evaluation.v ids.vio primitives.vio result_type.vio env.vio kernel_syntax.vio type_theory.vio elaboration.vio values.vio
evaluation.vos evaluation.vok evaluation.required_vos: evaluation.v ids.vos primitives.vos result_type.vos env.vos kernel_syntax.vos type_theory.vos elaboration.vos values.vos
