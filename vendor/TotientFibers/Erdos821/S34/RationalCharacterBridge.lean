module

public import Erdos821.P4Rat.RationalFourier
public import Erdos821.P4Rat.PrimitiveInduction
public import Erdos821.S34.RationalCharacterTasks

@[expose] public section

set_option autoImplicit false

namespace Erdos821.S34Core

theorem rationalFourierTask_proof : RationalFourierTask :=
  Erdos821.P4Rat.RationalFourierTask_proof

theorem primitiveInductionTask_proof : PrimitiveInductionTask :=
  Erdos821.P4Rat.PrimitiveInductionTask_proof

end Erdos821.S34Core
