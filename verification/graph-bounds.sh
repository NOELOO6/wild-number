#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
if [[ ${1:-bounds} == exact ]]; then
    "$root/verification/graph-bounds.sh" exact-k13
    "$root/verification/graph-bounds.sh" exact-k17
    "$root/verification/graph-bounds.sh" sieve
    exit 0
fi
lean=$(realpath "$(command -v "${LEAN:-lean}")")
lake="$(dirname "$lean")/lake"
export PATH="$(dirname "$lean"):$PATH"
mathlib=${MATHLIB_DIR:-"$root/.lake/graph-bounds-mathlib"}
if [[ ! -d "$mathlib" ]]; then
    mkdir -p "$(dirname "$mathlib")"
    git clone --depth 1 --branch v4.19.0 https://github.com/leanprover-community/mathlib4.git "$mathlib"
fi
cd "$mathlib"
revision=$(git rev-parse HEAD)
if [[ "$revision" != c44e0c8ee63ca166450922a373c7409c5d26b00b ]]; then
    echo 'Use the mathlib checkout at tag v4.19.0.' >&2
    exit 1
fi
if [[ ! -f .lake/build/lib/lean/Mathlib/GroupTheory/Perm/Sign.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Ring/Finset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Fin.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Group/Finset/Powerset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Perm.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Prod.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/BigOperators.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Powerset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/Order/BigOperators/Group/Finset.olean ]]; then
    "$lake" exe cache get Mathlib/GroupTheory/Perm/Sign.lean Mathlib/Algebra/BigOperators/Ring/Finset.lean \
      Mathlib/Data/Fintype/Perm.lean Mathlib/Data/Fintype/Prod.lean Mathlib/Data/Fintype/BigOperators.lean Mathlib/Algebra/BigOperators/Fin.lean \
      Mathlib/Data/Fintype/Powerset.lean Mathlib/Algebra/BigOperators/Group/Finset/Powerset.lean Mathlib/Algebra/Order/BigOperators/Group/Finset.lean
fi
if [[ ${1:-bounds} == sparse-orders || ${1:-bounds} == slots || ${1:-bounds} == regrouping || ${1:-bounds} == sieve || ${1:-bounds} == exact-k36 || ${1:-bounds} == k30 || ${1:-bounds} == large-orders || ${1:-bounds} == anchor-packing || ${1:-bounds} == exterior || ${1:-bounds} == palette19 ]]; then
    extras=(Mathlib/Combinatorics/Hall/Finite Mathlib/Data/ZMod/Basic Mathlib/Data/Fintype/Prod Mathlib/Data/List/Dedup Mathlib/Data/Int/GCD Mathlib/Tactic/Ring)
    if [[ ${1:-bounds} == sparse-orders || ${1:-bounds} == sieve || ${1:-bounds} == exact-k36 || ${1:-bounds} == k30 || ${1:-bounds} == large-orders || ${1:-bounds} == anchor-packing || ${1:-bounds} == exterior || ${1:-bounds} == palette19 ]]; then
        extras=(Mathlib/Tactic/Linarith Mathlib/Tactic/FieldSimp)
        if [[ ${1:-bounds} == sieve || ${1:-bounds} == large-orders ]]; then
            extras+=(Mathlib/Tactic/Ring Mathlib/Algebra/Order/Ring/Pow)
        fi
    fi
    if [[ ${1:-bounds} == k30 || ${1:-bounds} == sieve ]]; then
        extras+=(Mathlib/Algebra/Order/Field/Rat Mathlib/Algebra/BigOperators/Ring/List
            Mathlib/Data/List/FinRange Mathlib/Data/Multiset/Powerset Mathlib/Algebra/Ring/Parity
            Mathlib/Data/Fintype/EquivFin Mathlib/Tactic/Ring Mathlib/Tactic/NormNum)
    fi
    if [[ ${1:-bounds} == slots ]]; then
        extras=(Mathlib/LinearAlgebra/Dimension/Constructions Mathlib/LinearAlgebra/Dimension/Finite Mathlib/Combinatorics/Enumerative/DyckWord Mathlib/Order/PiLex Mathlib/Logic/Equiv/Fintype Mathlib/Data/Fintype/Sum Mathlib/Tactic/Ring)
    fi
    for module in "${extras[@]}"; do
        if [[ ! -f .lake/build/lib/lean/"$module".olean ]]; then
            "$lake" exe cache get "${extras[@]/%/.lean}"
            break
        fi
    done
fi
if [[ ( ${1:-bounds} == anchored || ${1:-bounds} == steiner-k15 ) && ! -f .lake/build/lib/lean/Mathlib/Dynamics/PeriodicPts/Lemmas.olean ]]; then
    "$lake" exe cache get Mathlib/Dynamics/PeriodicPts/Lemmas.lean
fi
if [[ ${1:-bounds} == steiner-k15 || ${1:-bounds} == cyclic-k21 || ${1:-bounds} == cyclic-k23 || ${1:-bounds} == cyclic-k25 || ${1:-bounds} == cyclic-k27 ]]; then
    modules=(Mathlib/Algebra/Group/Fin/Basic Mathlib/GroupTheory/Perm/ViaEmbedding Mathlib/Data/List/FinRange)
    if [[ ${1:-bounds} == cyclic-k25 || ${1:-bounds} == cyclic-k27 ]]; then modules+=(Mathlib/Data/ZMod/Defs); fi
    for module in "${modules[@]}"; do
        if [[ ! -f .lake/build/lib/lean/"$module".olean ]]; then
            "$lake" exe cache get "${modules[@]/%/.lean}"
            break
        fi
    done
fi
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build:$("$lake" env printenv LEAN_PATH)"
"$lean" --version
if [[ ${1:-bounds} == cyclic-k21 || ${1:-bounds} == cyclic-k23 || ${1:-bounds} == cyclic-k25 || ${1:-bounds} == cyclic-k27 ]]; then
    source "$root/verification/native.sh"
    native_module "$root/cases/k16/Delete.lean"
    native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
    n=${1#cyclic-k}
    native_module "$root/verification/exact/CyclicScan.lean" -lEdgeWalk -lDelete
    links=(-lCyclicScan -lEdgeWalk -lDelete)
    if [[ $n != 21 ]]; then
        native_module "$root/verification/exact/CyclicCuts.lean" "${links[@]}"
        links=(-lCyclicCuts "${links[@]}")
    fi
    if [[ $n == 25 || $n == 27 ]]; then
        native_module "$root/verification/exact/CyclicPrune.lean" "${links[@]}"
        links=(-lCyclicPrune "${links[@]}")
    fi
    native_module "$root/cases/k$n/Starters$n.lean" "${links[@]}"
    "$lean" --root="$root" --load-dynlib="$build/libStarters$n.$ext" -s 65536 \
        -o "$build/Cyclic${n}Check.olean" "$root/cases/k$n/Cyclic${n}Check.lean"
    files=(verification/exact/{ExactModel,UniversalLower,MatchingModel,CyclicExtraction}
        cases/k21/OrbitLayouts verification/exact/RotationalLayouts)
    if [[ $n == 21 ]]; then
        files+=(cases/regrouping/{TripleRepair,SymmetricRepair,ValidTriples} cases/k21/Extract21)
    fi
    if [[ $n != 21 ]]; then
        files+=(verification/exact/CyclicCutSound)
    fi
    if [[ $n == 25 || $n == 27 ]]; then files+=(verification/exact/CyclicNormal); fi
    files+=("cases/k$n/Cyclic$n")
    for file in "${files[@]}"; do
        "$lean" --root="$root" -s 65536 -o "$build/${file##*/}.olean" "$root/$file.lean"
    done
    exit 0
fi
if [[ ${1:-bounds} == steiner-k15 ]]; then
    source "$root/verification/native.sh"
    native_module "$root/cases/k16/Delete.lean"
    native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
    native_module "$root/verification/exact/CyclicScan.lean" -lEdgeWalk -lDelete
    native_module "$root/verification/exact/CyclicCuts.lean" -lCyclicScan -lEdgeWalk -lDelete
    links=(-lCyclicCuts -lCyclicScan -lEdgeWalk -lDelete)
    d="$root/cases/k15/steiner"
    native_module "$d/SteinerSearch.lean" "${links[@]}"
    native_module "$d/SteinerLayouts.lean" -lSteinerSearch "${links[@]}"
    "$lean" --root="$root" --load-dynlib="$build/libSteinerLayouts.$ext" -s 65536 \
        -o "$build/SteinerCheck.olean" "$d/SteinerCheck.lean"
    files=(cases/k19/LowerBound verification/graph-bounds/{UniformCuts,CutRepair,GraphLayouts}
        verification/exact/{ExactModel,UniversalLower,MatchingModel,SteinerSystem,CyclicExtraction}
        cases/k21/OrbitLayouts verification/exact/{RotationalLayouts,CyclicCutSound} cases/sieve/StarDraw
        cases/anchored/{PairFibers,PairPlacement,AnchoredGraph,PairTable,CycleTemplates,MaskSum,CycleLists,LocalFrames,AlternatingOrbits,AlternatingLists}
        cases/k15/steiner/{SteinerSystems,SteinerCoordinates,Steiner15,SteinerParity})
    for file in "${files[@]}"; do
        "$lean" --root="$root" -s 65536 -o "$build/${file##*/}.olean" "$root/$file.lean"
    done
    exit 0
fi
if [[ ${1:-bounds} == exact-k13 ]]; then
    source "$root/verification/exact-k13.sh"
    exit 0
fi
if [[ ${1:-bounds} == exact-k17 || ${1:-bounds} == exact-k17-pairs ]]; then
    source "$root/verification/exact-k17.sh"
    exit 0
fi
for file in "$root/cases/k16/Delete.lean" "$root/cases/k19/EdgeWalk.lean"; do
    "$lean" --root="$root" -o "$build/$(basename "$file" .lean).olean" "$file"
done
if [[ ${1:-bounds} != k30 && ${1:-bounds} != exact-k36 ]]; then
  "$lean" --root="$root" -o "$build/LowerBound.olean" "$root/cases/k19/LowerBound.lean"
  for name in UniformCuts CutRepair GraphLayouts ColorCoordinates LegalEdges Bounds; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/graph-bounds/$name.lean"
  done
fi
case ${1:-bounds} in
  bounds) ;;
  one-extra|anchored|slots)
    for name in ExactModel UniversalLower; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/exact/$name.lean"
    done
    "$lean" --root="$root" -s 65536 -o "$build/StarDraw.olean" "$root/cases/sieve/StarDraw.lean"
    if [[ ${1:-bounds} == anchored ]]; then
      "$lean" --root="$root" -s 65536 -o "$build/MatchingModel.olean" "$root/verification/exact/MatchingModel.lean"
      for name in PairFibers PairPlacement AnchoredGraph PairTable CycleTemplates MaskSum CycleLists Anchor24 Anchor30 Anchor36 \
          LocalFrames ThreeLabels CutSelection IncidenceCredit DisjointCuts PairCutCounts PairCutTable PairCutCheck NoFour30 \
          AlternatingOrbits AlternatingLists MatchingCycles SquareVertices ManyFour24 CycleCounts24 GraphCycles30; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/anchored/$name.lean"
      done
      exit 0
    fi
    if [[ ${1:-bounds} == slots ]]; then
      for name in NearCharge NearRange ThreeGroups CoreSplit TwoGroupCore CoreRange TwoCoreCheck TwoCore19 TwoCore23 Exchange21Data; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/one-extra/$name.lean"
      done
      for name in SlotCuts SmallSides ThreeSlots FourColors PaletteBound CutRank DecreasingTriples PaletteSizes CatalanBound SlotExamples SlotCases ReassignmentCheck QuartetCases QuintetCases OneReplacement; do
        "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/regrouping/slots/$name.lean"
      done
      if [[ ${2:-} == --count-k15 ]]; then
        "$root/verification/vertex-redraw.sh" "$lean" "$build" slot-count
      fi
      exit 0
    fi
    "$lean" --root="$root" -s 65536 -o "$build/MatchingModel.olean" "$root/verification/exact/MatchingModel.lean"
    for name in NearCharge NearRange ThreeGroups CoreSplit TwoGroupCore CoreRange CoreBudget CoreProfiles TwoCoreCheck Core21Data Core21Trap TwoCore19 TwoCore21 TwoCore23 CoreTransfer Exchange21Data Exchange21; do
      "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/one-extra/$name.lean"
    done
    ;;
  sparse-orders|sieve|exact-k36|k30|large-orders|anchor-packing|exterior|palette19)
    for name in ExactModel UniversalLower MatchingModel; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/exact/$name.lean"
    done
    for name in FiniteSieve Avoidance TripleParts TripleCounts Coupling Relabel TripleCoupling ClosedEvents SizeBounds MatchingCuts Factors Rainbow FrozenStats FrozenRows RowTotals DegreeChord FrozenLayout PlantedCuts StarDraw Numeric GraphSieve GraphRule; do
      "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
    done
    if [[ ${1:-bounds} == sparse-orders || ${1:-bounds} == sieve ]]; then
      "$lean" --root="$root" -s 65536 -o "$build/SteinerSystem.olean" "$root/verification/exact/SteinerSystem.lean"
      for name in SplitLayout RootTriples SparseOrders SteinerOrders; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
      if [[ ${1:-bounds} == sparse-orders ]]; then exit 0; fi
    fi
    check_large_orders() {
      for name in GeometricBounds GeometricLocal GeometricMass GeometricTail GeometricLarge GeometricRange ExactLarge; do
        "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
    }
    if [[ ${1:-bounds} == large-orders ]]; then
      for name in EvenTriples EvenRatios; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
      check_large_orders
      exit 0
    fi
    check_pattern_pairs() {
      for name in SixCounts TripleNeighbors WedgeCount TriplePatterns PatternPairs PatternGeometry; do
        "$lean" --root="$root" -j1 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
    }
    check_k30() {
      for name in JointDegrees EdgeDeletion MatchingSpectrum SealSpectrum RegionLayouts; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
      for name in CutModel30 CutPrices30 Budget30 Population30 Signature30 SixCounts30 GraphPopulation30 \
          Frame30 FrameCuts30 CellSpectrum30 ProfileBills30 SideSpectrum30 TripleNeighbors30 WedgeCount30 Patterns30 MomentPairs30 \
          MomentGeometry30 Restricted30 MotifCheck30 MotifRelabel30 MotifFive30 MotifLayout30 \
          OrderedMotifs30 MotifSum30 MotifRows30 LayoutMoments30 GraphBudget30 Sampling30 MarkedMeans30 DuplicateMeans30 FrameWeights30 FramePlacement30 \
          ActiveFrames30 FrameIncidence30 FrameColors30 Histogram30 OtherFrames30 SecondMeans30 GraphAverages30 \
          SignatureMeans30 GraphFunctional30 RowSums30 GraphRows30 Exact30 SmallDegrees30; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k30/$name.lean"
      done
    }
    check_k36() {
      check_pattern_pairs
      for name in SixCounts36 Multiplicity36 TripleNeighbors36 WedgeCount36 Patterns36 MomentPairs36 \
          MomentGeometry36 ChargeBounds36 TripleMotifs36 ShortMoment36 Region24 LongCuts36 Exact36; do
        "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/k36/$name.lean"
      done
    }
    if [[ ${1:-bounds} == exact-k36 || ${1:-bounds} == k30 ]]; then
      for name in EvenTriples TrimmedEvents InnerCuts LocalSeals PairRegions RootRegions RegionBudget \
          LayoutSplit MatchingSixes MixedSixes OverlapCredit LongCredit; do
        "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
      done
      if [[ ${1:-bounds} == k30 ]]; then
        check_pattern_pairs
        check_k30
      else
        check_k36
      fi
      exit 0
    fi
    if [[ ${1:-bounds} == palette19 ]]; then
      "$lean" --root="$root" -o "$build/Example19.olean" "$root/cases/k19/two-moves/Example19.lean"
      for name in PaletteData PaletteChecks PaletteGraph OrdinaryRedraw; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k19/four-colors/$name.lean"
      done
      exit 0
    fi
    if [[ ${1:-bounds} == exterior ]]; then
      source "$root/verification/nine-points.sh"
      for name in ExteriorData ExteriorPrices ExteriorTotals ExteriorPorts ExteriorAccounts ExteriorCuts ExteriorNine ExteriorGraph FiveTriples ExteriorSplit ResidualCuts ExteriorRepair; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k15/exterior/$name.lean"
      done
      exit 0
    fi
    if [[ ${1:-bounds} == anchor-packing ]]; then
      for name in AnchorPacking AnchorExample PackingColoring; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k15/half-packing/$name.lean"
      done
      for name in ColumnCount SevenSets RowPalettes BarrierRows RectangleRule RectangleGraph; do
        "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k15/rainbow-rectangle/$name.lean"
      done
      exit 0
    fi
    source "$root/verification/sieve-tables.sh"
    check_sieve_tables
    for name in KernelTables ExactRange TrimmedEvents InnerCuts TrimmedScopes LocalSeals PairRegions RootRegions RegionBudget MatchingRegions TrimmedLayout ExactTrimmed ExactSplit JointDegrees JointScopes ExactJoint ExactInterval EvenTriples EvenOrders LayoutSplit MatchingSixes MixedSixes SixGeometry42 OverlapCredit TripleSeal42 ShortCredit42 LongCredit Exact42 EvenRatios EvenSeries; do
      "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
    done
    check_k36
    check_k30
    check_large_orders
    "$lean" --root="$root" -s 65536 -o "$build/AllLarge.olean" "$root/cases/sieve/AllLarge.lean"
    "$lean" --root="$root" -j2 -s 65536 -o "$build/InfiniteEven.olean" "$root/cases/sieve/InfiniteEven.lean"
    "$lean" --root="$root" -s 65536 -o "$build/SixFamily.olean" "$root/cases/sieve/SixFamily.lean"
    "$lean" --root="$root" -s 65536 -o "$build/HalfMoment.olean" "$root/cases/k16/quartets/HalfMoment.lean"
    ;;
  regrouping)
    for name in ExactModel UniversalLower GraphSearch MatchingModel; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/exact/$name.lean"
    done
    "$lean" --root="$root" -o "$build/StarDraw.olean" "$root/cases/sieve/StarDraw.lean"
    "$lean" --root="$root" -o "$build/MatchingCuts.olean" "$root/cases/sieve/MatchingCuts.lean"
    for name in Periodic RoundRobin Reflection CyclicOrders TwoGroups CommonHalf MergeColors SwapExamples HalfTrap Bounds21 BridgeSwitch PartnerSwitch GraphSwitch OddSwitch DetourCount ChoosePoints SwitchCases; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/regrouping/$name.lean"
    done
    for name in QuartetTrap QuartetCount; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/k16/quartets/$name.lean"
    done
    ;;
  last-colors)
    "$lean" --root="$root" -o "$build/GraphCuts.olean" "$root/cases/k16/last-two/GraphCuts.lean"
    "$lean" --root="$root" -o "$build/Fourteen.olean" "$root/cases/k16/last-two/Fourteen.lean"
    for name in Example19 TwoMoves; do
      "$lean" --root="$root" -o "$build/$name.olean" "$root/cases/k19/two-moves/$name.lean"
    done
    ;;
  redraw)
    source "$root/verification/native.sh"
    redraw="$root/cases/k19/redraw"
    for name in MenuProof MenuTable SevenMore; do
      "$lean" --root="$redraw" -s 65536 -o "$build/$name.olean" "$redraw/$name.lean"
    done
    native_module "$redraw/LossTree.lean"
    native_module "$redraw/RawMenu.lean" -lLossTree
    for name in AllRoots TableLink EightBridge EightMore; do
      "$lean" --root="$redraw" --plugin="$build/libRawMenu.$ext" -j3 -s 65536 \
        -o "$build/$name.olean" "$redraw/$name.lean"
    done
    ;;
  pieces)
    pieces="$root/cases/k19/one-piece"
    for name in FiberMass BinMass GroupMerges PartitionCounts PieceTotals SmallAverage PieceBudget PiecePaths LastPiece; do
      "$lean" --root="$pieces" -s 65536 -o "$build/$name.olean" "$pieces/$name.lean"
    done
    ;;
  *) echo 'Use steiner-k15, sparse-orders, cyclic-k21, cyclic-k23, cyclic-k25, cyclic-k27, exact, exact-k36, large-orders, exact-k13, exact-k17, exact-k17-pairs, bounds, sieve, slots, anchored, exterior, palette19, anchor-packing, one-extra, regrouping, redraw, pieces or last-colors.' >&2; exit 2 ;;
esac
