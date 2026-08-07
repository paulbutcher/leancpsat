// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

// Compile-only: never linked into anything. Cross-checks every field number
// hand-declared in Cpsat/Proto.lean against protoc's own generated constants
// in cp_model.pb.h/sat_parameters.pb.h, so a transcription mistake, or a
// future OR-Tools upgrade that renumbers a field, fails to compile instead of
// silently corrupting the wire format.

#include "ortools/sat/cp_model.pb.h"
#include "ortools/sat/sat_parameters.pb.h"

namespace operations_research::sat {
namespace {

static_assert(IntegerVariableProto::kNameFieldNumber == 1);
static_assert(IntegerVariableProto::kDomainFieldNumber == 2);

static_assert(BoolArgumentProto::kLiteralsFieldNumber == 1);

static_assert(LinearExpressionProto::kVarsFieldNumber == 1);
static_assert(LinearExpressionProto::kCoeffsFieldNumber == 2);
static_assert(LinearExpressionProto::kOffsetFieldNumber == 3);

static_assert(LinearConstraintProto::kVarsFieldNumber == 1);
static_assert(LinearConstraintProto::kCoeffsFieldNumber == 2);
static_assert(LinearConstraintProto::kDomainFieldNumber == 3);

static_assert(AllDifferentConstraintProto::kExprsFieldNumber == 1);

static_assert(ElementConstraintProto::kLinearIndexFieldNumber == 4);
static_assert(ElementConstraintProto::kLinearTargetFieldNumber == 5);
static_assert(ElementConstraintProto::kExprsFieldNumber == 6);

static_assert(LinearArgumentProto::kTargetFieldNumber == 1);
static_assert(LinearArgumentProto::kExprsFieldNumber == 2);

static_assert(InverseConstraintProto::kFDirectFieldNumber == 1);
static_assert(InverseConstraintProto::kFInverseFieldNumber == 2);

static_assert(ConstraintProto::kNameFieldNumber == 1);
static_assert(ConstraintProto::kEnforcementLiteralFieldNumber == 2);
static_assert(ConstraintProto::kBoolOrFieldNumber == 3);
static_assert(ConstraintProto::kBoolAndFieldNumber == 4);
static_assert(ConstraintProto::kBoolXorFieldNumber == 5);
static_assert(ConstraintProto::kIntDivFieldNumber == 7);
static_assert(ConstraintProto::kIntModFieldNumber == 8);
static_assert(ConstraintProto::kIntProdFieldNumber == 11);
static_assert(ConstraintProto::kLinearFieldNumber == 12);
static_assert(ConstraintProto::kAllDiffFieldNumber == 13);
static_assert(ConstraintProto::kElementFieldNumber == 14);
static_assert(ConstraintProto::kInverseFieldNumber == 18);
static_assert(ConstraintProto::kAtMostOneFieldNumber == 26);
static_assert(ConstraintProto::kLinMaxFieldNumber == 27);
static_assert(ConstraintProto::kExactlyOneFieldNumber == 29);

static_assert(CpObjectiveProto::kVarsFieldNumber == 1);
static_assert(CpObjectiveProto::kOffsetFieldNumber == 2);
static_assert(CpObjectiveProto::kScalingFactorFieldNumber == 3);
static_assert(CpObjectiveProto::kCoeffsFieldNumber == 4);

static_assert(CpModelProto::kNameFieldNumber == 1);
static_assert(CpModelProto::kVariablesFieldNumber == 2);
static_assert(CpModelProto::kConstraintsFieldNumber == 3);
static_assert(CpModelProto::kObjectiveFieldNumber == 4);
static_assert(CpModelProto::kAssumptionsFieldNumber == 7);

static_assert(CpSolverResponse::kStatusFieldNumber == 1);
static_assert(CpSolverResponse::kSolutionFieldNumber == 2);
static_assert(CpSolverResponse::kObjectiveValueFieldNumber == 3);
static_assert(CpSolverResponse::kBestObjectiveBoundFieldNumber == 4);
static_assert(CpSolverResponse::kWallTimeFieldNumber == 15);
static_assert(CpSolverResponse::kSufficientAssumptionsForInfeasibilityFieldNumber == 23);

static_assert(SatParameters::kRandomSeedFieldNumber == 31);
static_assert(SatParameters::kMaxTimeInSecondsFieldNumber == 36);
static_assert(SatParameters::kLogSearchProgressFieldNumber == 41);
static_assert(SatParameters::kNumWorkersFieldNumber == 206);

}  // namespace
}  // namespace operations_research::sat
