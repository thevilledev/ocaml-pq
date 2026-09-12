#!/bin/sh
set -eu

source_dir=$1
target_dir=$2

mkdir -p "$target_dir/mlkem" "$target_dir/mldsa"
cp "$source_dir/LICENSE" "$target_dir/LICENSE"

for parameter in 512 768 1024; do
  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests[] |
      "id: \(.tcId)\nseed: \(.seed // $empty)\npublic_key: \(.ek // $empty)\nprivate_key: \(.dk // $empty)\nresult: \(.result)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mlkem_${parameter}_keygen_seed_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mlkem/mlkem_${parameter}_keygen_seed_test.txt"

  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests[] |
      ((.flags // []) | join(",")) as $flags |
      "id: \(.tcId)\nseed: \(.seed // $empty)\npublic_key: \(.ek // $empty)\nciphertext: \(.c // $empty)\nshared_secret: \(.K // $empty)\nresult: \(.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mlkem_${parameter}_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mlkem/mlkem_${parameter}_test.txt"

  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests[] |
      ((.flags // []) | join(",")) as $flags |
      "id: \(.tcId)\npublic_key: \(.ek // $empty)\nrandomness: \(.m // $empty)\nciphertext: \(.c // $empty)\nshared_secret: \(.K // $empty)\nresult: \(.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mlkem_${parameter}_encaps_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mlkem/mlkem_${parameter}_encaps_test.txt"

  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests[] |
      ((.flags // []) | join(",")) as $flags |
      "id: \(.tcId)\nprivate_key: \(.dk // $empty)\npublic_key: \(.ek // $empty)\nciphertext: \(.c // $empty)\nshared_secret: \(.K // $empty)\nresult: \(.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mlkem_${parameter}_semi_expanded_decaps_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mlkem/mlkem_${parameter}_semi_expanded_decaps_test.txt"
done

for parameter in 44 65 87; do
  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests | to_entries[] |
      .key as $index | .value as $test |
      (($test.flags // []) | join(",")) as $flags |
      (if ($test.flags // []) | index("Internal") then "internal" else "external" end) as $interface |
      (if $index == 0 then "new" else $empty end) as $group_marker |
      "id: \($test.tcId)\ngroup: \($group_marker)\nprivate_key: \(if $index == 0 then ($group.privateSeed // $empty) else $empty end)\npublic_key: \(if $index == 0 then ($group.publicKey // $empty) else $empty end)\ninterface: \($interface)\nmessage: \($test.msg // $empty)\ncontext: \($test.ctx // $empty)\nmu: \($test.mu // $empty)\nrandomness: \($test.rnd // $empty)\nsignature: \($test.sig // $empty)\nresult: \($test.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mldsa_${parameter}_sign_seed_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mldsa/mldsa_${parameter}_sign_seed_test.txt"

  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests | to_entries[] |
      .key as $index | .value as $test |
      (($test.flags // []) | join(",")) as $flags |
      (if ($test.flags // []) | index("Internal") then "internal" else "external" end) as $interface |
      (if $index == 0 then "new" else $empty end) as $group_marker |
      "id: \($test.tcId)\ngroup: \($group_marker)\nprivate_key: \(if $index == 0 then ($group.privateKey // $empty) else $empty end)\npublic_key: \(if $index == 0 then ($group.publicKey // $empty) else $empty end)\ninterface: \($interface)\nmessage: \($test.msg // $empty)\ncontext: \($test.ctx // $empty)\nmu: \($test.mu // $empty)\nrandomness: \($test.rnd // $empty)\nsignature: \($test.sig // $empty)\nresult: \($test.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mldsa_${parameter}_sign_noseed_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mldsa/mldsa_${parameter}_sign_noseed_test.txt"

  jq -jr '
    "" as $empty |
    [.testGroups[] as $group | $group.tests | to_entries[] |
      .key as $index | .value as $test |
      (($test.flags // []) | join(",")) as $flags |
      (if $index == 0 then "new" else $empty end) as $group_marker |
      "id: \($test.tcId)\ngroup: \($group_marker)\npublic_key: \(if $index == 0 then ($group.publicKey // $empty) else $empty end)\nmessage: \($test.msg // $empty)\ncontext: \($test.ctx // $empty)\nsignature: \($test.sig // $empty)\nresult: \($test.result)\nflags: \($flags)"
    ] | join("\n\n") + "\n"
  ' "$source_dir/testvectors_v1/mldsa_${parameter}_verify_test.json" \
    | sed 's/: $/:/' \
    > "$target_dir/mldsa/mldsa_${parameter}_verify_test.txt"
done
