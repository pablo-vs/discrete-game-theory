#!/usr/bin/env python3
"""
Search for counterexamples to claims about BR/mix behavior in Synthetic Game Theory.

Examples:
  # Random sample 10k 3x3 games and search for a counterexample to BR(mix)=union(BR)
  python scripts/search_counterexamples.py --actions 3 3 --samples 10000 --check br_mix_eq_union

  # Random sample 100k 3x3x3 games and check if there is always a Nash equilibrium
  python scripts/search_counterexamples.py --actions 3 3 3 --samples 100000 --check nash_exists

  # Random sample 50k 3x3x3 games and check the "exists a,b" claim
  python scripts/search_counterexamples.py --actions 3 3 3 --samples 50000 --check exists_ab
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple


Face = int
Profile = Tuple[Face, ...]


@dataclass
class Game:
    action_counts: List[int]
    ranks: List[List[int]]  # ranks[player][profile_index]

    def __post_init__(self) -> None:
        self.n = len(self.action_counts)
        self.pure_profiles = list(itertools.product(*[range(m) for m in self.action_counts]))
        self.profile_index = {p: i for i, p in enumerate(self.pure_profiles)}
        self._opp_action_tuples = self._precompute_opp_action_tuples()
        self._action_le_cache: Dict[Tuple[int, Tuple[Face, ...], int, int], bool] = {}

    def le(self, i: int, p: Tuple[int, ...], q: Tuple[int, ...]) -> bool:
        return self.ranks[i][self.profile_index[p]] <= self.ranks[i][self.profile_index[q]]

    def _precompute_opp_action_tuples(self) -> List[Dict[Tuple[Face, ...], List[Tuple[int, ...]]]]:
        result: List[Dict[Tuple[Face, ...], List[Tuple[int, ...]]]] = []
        for i in range(self.n):
            opp_players = [j for j in range(self.n) if j != i]
            opp_faces_lists = [all_faces(self.action_counts[j]) for j in opp_players]
            mapping: Dict[Tuple[Face, ...], List[Tuple[int, ...]]] = {}
            for opp_faces in itertools.product(*opp_faces_lists):
                action_lists = [face_to_actions(face, self.action_counts[j]) for face, j in zip(opp_faces, opp_players)]
                mapping[opp_faces] = list(itertools.product(*action_lists))
            result.append(mapping)
        return result

    def _profile_from_action(self, i: int, action: int, opp_actions: Tuple[int, ...]) -> Tuple[int, ...]:
        profile: List[int] = []
        opp_idx = 0
        for j in range(self.n):
            if j == i:
                profile.append(action)
            else:
                profile.append(opp_actions[opp_idx])
                opp_idx += 1
        return tuple(profile)

    def action_le(self, i: int, opp_faces: Tuple[Face, ...], a: int, b: int) -> bool:
        key = (i, opp_faces, a, b)
        cached = self._action_le_cache.get(key)
        if cached is not None:
            return cached
        opp_action_tuples = self._opp_action_tuples[i][opp_faces]
        for s in opp_action_tuples:
            p = self._profile_from_action(i, a, s)
            for t in opp_action_tuples:
                q = self._profile_from_action(i, b, t)
                if not self.le(i, p, q):
                    self._action_le_cache[key] = False
                    return False
        self._action_le_cache[key] = True
        return True

    def action_dominated(self, i: int, opp_faces: Tuple[Face, ...], a: int) -> bool:
        for b in range(self.action_counts[i]):
            if a == b:
                continue
            if self.action_le(i, opp_faces, a, b) and not self.action_le(i, opp_faces, b, a):
                return True
        return False

    def br_actions(self, i: int, opp_faces: Tuple[Face, ...]) -> List[int]:
        return [a for a in range(self.action_counts[i]) if not self.action_dominated(i, opp_faces, a)]


# --- helpers ---

def all_faces(m: int) -> List[Face]:
    return list(range(1, 1 << m))


def face_to_actions(face: Face, m: int) -> List[int]:
    return [a for a in range(m) if (face >> a) & 1]


def actions_to_face(actions: Iterable[int]) -> Face:
    face = 0
    for a in actions:
        face |= 1 << a
    return face


def mix_faces(f1: Face, f2: Face) -> Face:
    return f1 | f2


def mix_profiles(p: Profile, q: Profile) -> Profile:
    return tuple(mix_faces(a, b) for a, b in zip(p, q))


def profile_to_lists(profile: Profile, action_counts: Sequence[int]) -> List[List[int]]:
    return [face_to_actions(face, action_counts[i]) for i, face in enumerate(profile)]


def random_game(action_counts: List[int], rng: random.Random, rank_range: int | None) -> Game:
    num_profiles = math.prod(action_counts)
    max_rank = rank_range if rank_range is not None else num_profiles
    ranks: List[List[int]] = []
    for _ in range(len(action_counts)):
        ranks.append([rng.randrange(max_rank) for _ in range(num_profiles)])
    return Game(action_counts=action_counts, ranks=ranks)


def all_profiles(action_counts: Sequence[int]) -> List[Profile]:
    face_lists = [all_faces(m) for m in action_counts]
    return list(itertools.product(*face_lists))


def opponent_faces(profile: Profile, i: int) -> Tuple[Face, ...]:
    return tuple(profile[j] for j in range(len(profile)) if j != i)


def has_nash_equilibrium(game: Game, profiles: Sequence[Profile]) -> Tuple[bool, Profile | None]:
    for profile in profiles:
        ok = True
        for i in range(game.n):
            br = set(game.br_actions(i, opponent_faces(profile, i)))
            if not set(face_to_actions(profile[i], game.action_counts[i])).issubset(br):
                ok = False
                break
        if ok:
            return True, profile
    return False, None


# --- claims ---

class Claim:
    BR_MIX_EQ_UNION = "br_mix_eq_union"
    BR_MIX_SUBSET_UNION = "br_mix_subset_union"
    MIX_OF_UNDOMINATED = "mix_of_undominated"
    EXISTS_AB = "exists_ab"
    SUPPORT_FACES_BR_EACH_OTHER = "support_faces_br_each_other"
    SUPPORT_SUBFACE_NASH = "support_subface_nash"
    SUPPORT_KKM = "support_kkm"
    SUPPORT_DEF_NONEMPTY = "support_def_nonempty"
    NASH_EXISTS = "nash_exists"


def check_claims(
    game: Game,
    claims: List[str],
    profiles: Sequence[Profile],
) -> Tuple[bool, Dict[str, object]]:
    for claim in claims:
        br_by_profile: List[Dict[Profile, set[int]]] | None = None
        if claim == Claim.SUPPORT_SUBFACE_NASH:
            br_by_profile = [
                {profile: set(game.br_actions(i, opponent_faces(profile, i))) for profile in profiles}
                for i in range(game.n)
            ]
        if claim == Claim.SUPPORT_KKM:
            br_by_profile = [
                {profile: set(game.br_actions(i, opponent_faces(profile, i))) for profile in profiles}
                for i in range(game.n)
            ]
        if claim == Claim.SUPPORT_DEF_NONEMPTY:
            br_by_profile = [
                {profile: set(game.br_actions(i, opponent_faces(profile, i))) for profile in profiles}
                for i in range(game.n)
            ]
        if claim == Claim.NASH_EXISTS:
            ok, witness = has_nash_equilibrium(game, profiles)
            if not ok:
                return False, {
                    "claim": claim,
                    "message": "No Nash equilibrium found.",
                }
            continue

        # Claims that involve mixing two profiles
        for p in profiles:
            for q in profiles:
                mix = mix_profiles(p, q)
                if claim == Claim.SUPPORT_FACES_BR_EACH_OTHER:
                    if not (_profile_in_br_profile(game, p, q) and _profile_in_br_profile(game, q, p) and p != q):
                        continue
                    ok, payload = _check_support_faces_br_each_other(game, p, q, mix)
                    if not ok:
                        return False, payload
                    continue
                if claim == Claim.SUPPORT_SUBFACE_NASH:
                    if not _strict_two_cycle_cached(game, p, q, br_by_profile):
                        continue
                    ok, payload = _check_support_subface_nash(game, p, q, mix, br_by_profile)
                    if not ok:
                        return False, payload
                    continue
                if claim == Claim.SUPPORT_KKM:
                    if not _strict_two_cycle_cached(game, p, q, br_by_profile):
                        continue
                    ok, payload = _check_support_kkm(game, p, q, mix, br_by_profile)
                    if not ok:
                        return False, payload
                    continue
                if claim == Claim.SUPPORT_DEF_NONEMPTY:
                    if not _strict_two_cycle_cached(game, p, q, br_by_profile):
                        continue
                    ok, payload = _check_support_def_nonempty(game, p, q, mix)
                    if not ok:
                        return False, payload
                    continue
                for i in range(game.n):
                    br_p = set(game.br_actions(i, opponent_faces(p, i)))
                    br_q = set(game.br_actions(i, opponent_faces(q, i)))
                    br_m = set(game.br_actions(i, opponent_faces(mix, i)))

                    if claim == Claim.BR_MIX_EQ_UNION:
                        if br_m != (br_p | br_q):
                            return False, _counterexample_payload(
                                game, claim, p, q, i, br_p, br_q, br_m
                            )

                    elif claim == Claim.BR_MIX_SUBSET_UNION:
                        if not br_m.issubset(br_p | br_q):
                            return False, _counterexample_payload(
                                game, claim, p, q, i, br_p, br_q, br_m
                            )

                    elif claim == Claim.MIX_OF_UNDOMINATED:
                        for a in br_p:
                            for b in br_q:
                                if not ({a, b}.issubset(br_m)):
                                    return False, _counterexample_payload(
                                        game,
                                        claim,
                                        p,
                                        q,
                                        i,
                                        br_p,
                                        br_q,
                                        br_m,
                                        extra={"a": a, "b": b},
                                    )

                    elif claim == Claim.EXISTS_AB:
                        if not (br_p & br_m) or not (br_q & br_m):
                            return False, _counterexample_payload(
                                game, claim, p, q, i, br_p, br_q, br_m
                            )

    return True, {}


def _counterexample_payload(
    game: Game,
    claim: str,
    p: Profile,
    q: Profile,
    player: int,
    br_p: set[int],
    br_q: set[int],
    br_m: set[int],
    extra: Dict[str, object] | None = None,
) -> Dict[str, object]:
    payload: Dict[str, object] = {
        "claim": claim,
        "player": player,
        "action_counts": game.action_counts,
        "profile_p": profile_to_lists(p, game.action_counts),
        "profile_q": profile_to_lists(q, game.action_counts),
        "profile_mix": profile_to_lists(mix_profiles(p, q), game.action_counts),
        "br_p": sorted(br_p),
        "br_q": sorted(br_q),
        "br_mix": sorted(br_m),
        "ranks": game.ranks,
    }
    if extra:
        payload.update(extra)
    return payload


def _profile_in_br_profile(game: Game, p: Profile, q: Profile) -> bool:
    for i in range(game.n):
        br = set(game.br_actions(i, opponent_faces(q, i)))
        if not set(face_to_actions(p[i], game.action_counts[i])).issubset(br):
            return False
    return True


def _strict_two_cycle(game: Game, p: Profile, q: Profile) -> bool:
    if p == q:
        return False
    for i in range(game.n):
        br_q = set(game.br_actions(i, opponent_faces(q, i)))
        br_p = set(game.br_actions(i, opponent_faces(p, i)))
        p_actions = set(face_to_actions(p[i], game.action_counts[i]))
        q_actions = set(face_to_actions(q[i], game.action_counts[i]))
        if br_q != p_actions or br_p != q_actions:
            return False
    return True


def _strict_two_cycle_cached(
    game: Game,
    p: Profile,
    q: Profile,
    br_by_profile: List[Dict[Profile, set[int]]] | None,
) -> bool:
    if br_by_profile is None:
        return _strict_two_cycle(game, p, q)
    if p == q:
        return False
    for i in range(game.n):
        br_q = br_by_profile[i][q]
        br_p = br_by_profile[i][p]
        p_actions = set(face_to_actions(p[i], game.action_counts[i]))
        q_actions = set(face_to_actions(q[i], game.action_counts[i]))
        if br_q != p_actions or br_p != q_actions:
            return False
    return True


def _check_support_faces_br_each_other(
    game: Game,
    p: Profile,
    q: Profile,
    mix: Profile,
) -> Tuple[bool, Dict[str, object]]:
    support_actions: List[set[int]] = []
    for i in range(game.n):
        br_p = set(game.br_actions(i, opponent_faces(p, i)))
        br_q = set(game.br_actions(i, opponent_faces(q, i)))
        br_m = set(game.br_actions(i, opponent_faces(mix, i)))
        support_actions.append((br_p & br_m) | (br_q & br_m))

    if any(not actions for actions in support_actions):
        return False, {
            "claim": Claim.SUPPORT_FACES_BR_EACH_OTHER,
            "message": "Empty support face for at least one player.",
            "action_counts": game.action_counts,
            "profile_p": profile_to_lists(p, game.action_counts),
            "profile_q": profile_to_lists(q, game.action_counts),
            "profile_mix": profile_to_lists(mix, game.action_counts),
            "support_actions": [sorted(list(actions)) for actions in support_actions],
            "ranks": game.ranks,
        }

    support_profile = tuple(actions_to_face(actions) for actions in support_actions)
    for i in range(game.n):
        br_support = set(game.br_actions(i, opponent_faces(support_profile, i)))
        support_face_actions = set(face_to_actions(support_profile[i], game.action_counts[i]))
        if not support_face_actions.issubset(br_support):
            return False, {
                "claim": Claim.SUPPORT_FACES_BR_EACH_OTHER,
                "action_counts": game.action_counts,
                "profile_p": profile_to_lists(p, game.action_counts),
                "profile_q": profile_to_lists(q, game.action_counts),
                "profile_mix": profile_to_lists(mix, game.action_counts),
                "support_profile": profile_to_lists(support_profile, game.action_counts),
                "support_actions": [sorted(list(actions)) for actions in support_actions],
                "player": i,
                "br_support": sorted(br_support),
                "ranks": game.ranks,
            }

    return True, {}


def _check_support_subface_nash(
    game: Game,
    p: Profile,
    q: Profile,
    mix: Profile,
    br_by_profile: List[Dict[Profile, set[int]]] | None,
) -> Tuple[bool, Dict[str, object]]:
    support_actions: List[List[int]] = []
    for i in range(game.n):
        if br_by_profile is None:
            br_p = set(game.br_actions(i, opponent_faces(p, i)))
            br_q = set(game.br_actions(i, opponent_faces(q, i)))
            br_m = set(game.br_actions(i, opponent_faces(mix, i)))
        else:
            br_p = br_by_profile[i][p]
            br_q = br_by_profile[i][q]
            br_m = br_by_profile[i][mix]
        actions = sorted((br_p & br_m) | (br_q & br_m))
        if not actions:
            return False, {
                "claim": Claim.SUPPORT_SUBFACE_NASH,
                "message": "Empty support face for at least one player.",
                "action_counts": game.action_counts,
                "profile_p": profile_to_lists(p, game.action_counts),
                "profile_q": profile_to_lists(q, game.action_counts),
                "profile_mix": profile_to_lists(mix, game.action_counts),
                "support_actions": support_actions,
                "ranks": game.ranks,
            }
        support_actions.append(actions)

    subfaces = []
    for actions in support_actions:
        masks = range(1, 1 << len(actions))
        faces = [actions_to_face(actions[j] for j in range(len(actions)) if (mask >> j) & 1) for mask in masks]
        subfaces.append(faces)

    for candidate in itertools.product(*subfaces):
        ok = True
        for i in range(game.n):
            if br_by_profile is None:
                br = set(game.br_actions(i, opponent_faces(candidate, i)))
            else:
                br = br_by_profile[i][candidate]
            cand_actions = set(face_to_actions(candidate[i], game.action_counts[i]))
            if not cand_actions.issubset(br):
                ok = False
                break
        if ok:
            return True, {}

    return False, {
        "claim": Claim.SUPPORT_SUBFACE_NASH,
        "action_counts": game.action_counts,
        "profile_p": profile_to_lists(p, game.action_counts),
        "profile_q": profile_to_lists(q, game.action_counts),
        "profile_mix": profile_to_lists(mix, game.action_counts),
        "support_actions": support_actions,
        "ranks": game.ranks,
    }


def _check_support_kkm(
    game: Game,
    p: Profile,
    q: Profile,
    mix: Profile,
    br_by_profile: List[Dict[Profile, set[int]]] | None,
) -> Tuple[bool, Dict[str, object]]:
    if br_by_profile is None:
        raise ValueError("support_kkm requires br_by_profile")

    support_actions: List[List[int]] = []
    for i in range(game.n):
        br_p = br_by_profile[i][p]
        br_q = br_by_profile[i][q]
        br_m = br_by_profile[i][mix]
        actions = sorted((br_p & br_m) | (br_q & br_m))
        if not actions:
            return False, {
                "claim": Claim.SUPPORT_KKM,
                "message": "Empty support face for at least one player.",
                "action_counts": game.action_counts,
                "profile_p": profile_to_lists(p, game.action_counts),
                "profile_q": profile_to_lists(q, game.action_counts),
                "profile_mix": profile_to_lists(mix, game.action_counts),
                "support_actions": support_actions,
                "ranks": game.ranks,
            }
        support_actions.append(actions)

    subfaces = []
    for actions in support_actions:
        masks = range(1, 1 << len(actions))
        faces = [actions_to_face(actions[j] for j in range(len(actions)) if (mask >> j) & 1) for mask in masks]
        subfaces.append(faces)

    for candidate in itertools.product(*subfaces):
        for i in range(game.n):
            br = br_by_profile[i][candidate]
            if not (br & set(support_actions[i])):
                return False, {
                    "claim": Claim.SUPPORT_KKM,
                    "action_counts": game.action_counts,
                    "profile_p": profile_to_lists(p, game.action_counts),
                    "profile_q": profile_to_lists(q, game.action_counts),
                    "profile_mix": profile_to_lists(mix, game.action_counts),
                    "support_actions": support_actions,
                    "candidate": profile_to_lists(candidate, game.action_counts),
                    "player": i,
                    "br_candidate": sorted(br),
                    "ranks": game.ranks,
                }

    return True, {}


def _check_support_def_nonempty(
    game: Game,
    p: Profile,
    q: Profile,
    mix: Profile,
) -> Tuple[bool, Dict[str, object]]:
    support_actions: List[List[int]] = []
    for i in range(game.n):
        br_p = set(game.br_actions(i, opponent_faces(p, i)))
        br_q = set(game.br_actions(i, opponent_faces(q, i)))
        br_m = set(game.br_actions(i, opponent_faces(mix, i)))
        actions = sorted((br_p & br_m) | (br_q & br_m))
        if not actions:
            return False, {
                "claim": Claim.SUPPORT_DEF_NONEMPTY,
                "message": "Empty support face for at least one player.",
                "action_counts": game.action_counts,
                "profile_p": profile_to_lists(p, game.action_counts),
                "profile_q": profile_to_lists(q, game.action_counts),
                "profile_mix": profile_to_lists(mix, game.action_counts),
                "support_actions": support_actions,
                "ranks": game.ranks,
            }
        support_actions.append(actions)

    for i in range(game.n):
        opp_players = [j for j in range(game.n) if j != i]
        opp_faces = tuple(actions_to_face(support_actions[j]) for j in opp_players)
        for a in support_actions[i]:
            defended = True
            for b in support_actions[i]:
                if a == b:
                    continue
                if not game.action_le(i, opp_faces, b, a):
                    defended = False
                    break
            if defended:
                break
        else:
            return False, {
                "claim": Claim.SUPPORT_DEF_NONEMPTY,
                "action_counts": game.action_counts,
                "profile_p": profile_to_lists(p, game.action_counts),
                "profile_q": profile_to_lists(q, game.action_counts),
                "profile_mix": profile_to_lists(mix, game.action_counts),
                "support_actions": support_actions,
                "player": i,
                "ranks": game.ranks,
            }

    return True, {}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--actions", type=int, nargs="+", required=True, help="Actions per player, e.g. 3 3 3")
    parser.add_argument("--samples", type=int, default=1000, help="Number of random games to sample")
    parser.add_argument("--seed", type=int, default=0, help="Random seed")
    parser.add_argument(
        "--rank-range",
        type=int,
        default=None,
        help="Upper bound (exclusive) for random ranks; default = number of pure profiles",
    )
    parser.add_argument(
        "--check",
        type=str,
        nargs="+",
        default=[Claim.NASH_EXISTS],
        choices=[
            Claim.BR_MIX_EQ_UNION,
            Claim.BR_MIX_SUBSET_UNION,
            Claim.MIX_OF_UNDOMINATED,
            Claim.EXISTS_AB,
            Claim.SUPPORT_FACES_BR_EACH_OTHER,
            Claim.SUPPORT_SUBFACE_NASH,
            Claim.SUPPORT_KKM,
            Claim.SUPPORT_DEF_NONEMPTY,
            Claim.NASH_EXISTS,
        ],
        help="Claims to test",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rng = random.Random(args.seed)
    profiles = all_profiles(args.actions)

    for sample_idx in range(1, args.samples + 1):
        game = random_game(args.actions, rng, args.rank_range)
        ok, payload = check_claims(game, args.check, profiles)
        if not ok:
            print(json.dumps({"sample": sample_idx, "counterexample": payload}, indent=2))
            return

    print(
        json.dumps(
            {
                "status": "no_counterexample",
                "samples": args.samples,
                "actions": args.actions,
                "checks": args.check,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
