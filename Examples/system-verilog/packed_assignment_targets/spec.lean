import Examples.«system-verilog».packed_assignment_targets.proof

namespace Examples.systemVerilog.packedAssignmentTargets

open LeanModels.Sv LeanModels.Sv.SelfCheck

def assignAtUnknownIndex (value : LVec) : Res (SvState × NbaQueue × Out) :=
  proof.writeUnknown value

theorem unknown_index_preserves_state (value : LVec) :
    assignAtUnknownIndex value = .ok (proof.unknownFrame value, [], {}) :=
  proof.unknown_index_preserves_state value

#print axioms unknown_index_preserves_state

def assignAliasedDestinations (value : LVec) : Res (SvState × NbaQueue × Out) :=
  proof.writeAlias value rightToLeftAssignmentOrder

theorem alias_right_to_left (value : LVec) (width : value.width = 4) :
    assignAliasedDestinations value = .ok ([("first", .lit "1010")], [], {}) :=
  proof.alias_right_to_left value width

theorem alias_invalid_order_refused (value : LVec) :
    proof.writeAlias value (fun _ => [0, 0]) =
      .unsupported "concatenated assignment order must be a permutation of destinations" :=
  proof.alias_invalid_order_refused value

#print axioms alias_right_to_left
#print axioms alias_invalid_order_refused

end Examples.systemVerilog.packedAssignmentTargets
