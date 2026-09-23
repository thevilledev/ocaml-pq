type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string
  | Context_too_long of int

let pp_error formatter = function
  | Invalid_length { what; expected; actual } ->
      Format.fprintf formatter "%s has length %d, expected %d" what actual expected
  | Invalid_encoding message -> Format.pp_print_string formatter message
  | Context_too_long length ->
      Format.fprintf formatter "context has length %d, expected at most 255" length

module type PARAMETERS = sig
  val name : string
  val hash : [ `Sha2 | `Shake ]
  val n : int
  val h : int
  val d : int
  val a : int
  val k : int
  val m : int
end

module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int

  val pp_error : Format.formatter -> error -> unit

  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key

  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string

  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string

  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
end

module type INTERNAL = sig
  include S

  val sign_internal_for_testing :
    signing_key ->
    formatted_message:string ->
    randomness:string ->
    (signature, error) result

  val verify_internal_for_testing :
    verification_key -> formatted_message:string -> signature -> bool

  val fors_tree_for_testing :
    sk_seed:string -> pk_seed:string -> leaf_index:int -> string * string
end

module Make (P : PARAMETERS) : INTERNAL = struct
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int

  let pp_error = pp_error

  let wots_w = 16
  let wots_len1 = 2 * P.n
  let wots_len2 = 3
  let wots_len = wots_len1 + wots_len2
  let tree_height = P.h / P.d
  let fors_message_bytes = ((P.k * P.a) + 7) / 8
  let tree_bits = tree_height * (P.d - 1)
  let tree_bytes = (tree_bits + 7) / 8
  let leaf_bytes = (tree_height + 7) / 8

  let seed_size = 3 * P.n
  let signing_key_size = 4 * P.n
  let verification_key_size = 2 * P.n
  let fors_signature_size = P.k * (P.a + 1) * P.n
  let wots_signature_size = wots_len * P.n

  let signature_size =
    P.n + fors_signature_size
    + (P.d * (wots_signature_size + (tree_height * P.n)))

  let () =
    if P.h mod P.d <> 0 then invalid_arg (P.name ^ ": h must be divisible by d");
    if fors_message_bytes + tree_bytes + leaf_bytes <> P.m then
      invalid_arg (P.name ^ ": inconsistent message-digest length");
    if tree_bits > 64 then invalid_arg (P.name ^ ": tree address exceeds 64 bits")

  type verification_key = {
    pk_seed : string;
    pk_root : string;
  }

  type signing_key = {
    sk_seed : string;
    sk_prf : string;
    verification_key : verification_key;
    seed : string option;
  }

  type signature = string

  type address = {
    layer : int;
    tree : int64;
    typ : int;
    keypair : int;
    field1 : int;
    field2 : int;
  }

  type hash_context = {
    sk_seed : string;
    pk_seed : string;
  }

  let zero_address =
    { layer = 0; tree = 0L; typ = 0; keypair = 0; field1 = 0; field2 = 0 }

  let invalid_length what expected value =
    Error (Invalid_length { what; expected; actual = String.length value })

  let sub = String.sub

  let truncate length value =
    if String.length value = length then value else String.sub value 0 length

  let set_u32_be bytes offset value =
    Bytes.unsafe_set bytes offset (Char.unsafe_chr ((value lsr 24) land 0xff));
    Bytes.unsafe_set bytes (offset + 1)
      (Char.unsafe_chr ((value lsr 16) land 0xff));
    Bytes.unsafe_set bytes (offset + 2)
      (Char.unsafe_chr ((value lsr 8) land 0xff));
    Bytes.unsafe_set bytes (offset + 3) (Char.unsafe_chr (value land 0xff))

  let set_u64_be bytes offset value =
    for i = 0 to 7 do
      Bytes.unsafe_set bytes (offset + i)
        (Char.unsafe_chr
           (Int64.to_int
              (Int64.logand
                 (Int64.shift_right_logical value (8 * (7 - i)))
                 0xffL)))
    done

  let address_full address =
    let result = Bytes.make 32 '\000' in
    set_u32_be result 0 address.layer;
    set_u64_be result 8 address.tree;
    set_u32_be result 16 address.typ;
    set_u32_be result 20 address.keypair;
    set_u32_be result 24 address.field1;
    set_u32_be result 28 address.field2;
    Bytes.unsafe_to_string result

  let address_compressed address =
    let result = Bytes.make 22 '\000' in
    Bytes.unsafe_set result 0 (Char.unsafe_chr address.layer);
    set_u64_be result 1 address.tree;
    Bytes.unsafe_set result 9 (Char.unsafe_chr address.typ);
    set_u32_be result 10 address.keypair;
    set_u32_be result 14 address.field1;
    set_u32_be result 18 address.field2;
    Bytes.unsafe_to_string result

  let with_type typ address = { address with typ }

  let keypair_address typ source =
    {
      layer = source.layer;
      tree = source.tree;
      typ;
      keypair = source.keypair;
      field1 = 0;
      field2 = 0;
    }

  let subtree_address typ source =
    { zero_address with layer = source.layer; tree = source.tree; typ }

  let sha2_prefix block_size seed =
    seed ^ String.make (block_size - String.length seed) '\000'

  let thash context address input_blocks =
    let input = String.concat "" input_blocks in
    match P.hash with
    | `Shake ->
        Slhdsa_hash.shake256 ~output_length:P.n
          (context.pk_seed ^ address_full address ^ input)
    | `Sha2 ->
        if P.n >= 24 && List.length input_blocks > 1 then
          truncate P.n
            (Slhdsa_hash.sha512
               (sha2_prefix 128 context.pk_seed ^ address_compressed address ^ input))
        else
          truncate P.n
            (Slhdsa_hash.sha256
               (sha2_prefix 64 context.pk_seed ^ address_compressed address ^ input))

  let prf context address =
    match P.hash with
    | `Shake ->
        Slhdsa_hash.shake256 ~output_length:P.n
          (context.pk_seed ^ address_full address ^ context.sk_seed)
    | `Sha2 ->
        truncate P.n
          (Slhdsa_hash.sha256
             (sha2_prefix 64 context.pk_seed ^ address_compressed address
              ^ context.sk_seed))

  let prf_message sk_prf randomness message =
    match P.hash with
    | `Shake ->
        Slhdsa_hash.shake256 ~output_length:P.n
          (sk_prf ^ randomness ^ message)
    | `Sha2 ->
        truncate P.n
          (if P.n = 16 then
             Slhdsa_hash.hmac_sha256 sk_prf (randomness ^ message)
           else Slhdsa_hash.hmac_sha512 sk_prf (randomness ^ message))

  let hash_message randomizer (verification_key : verification_key) message =
    let public_key = verification_key.pk_seed ^ verification_key.pk_root in
    match P.hash with
    | `Shake ->
        Slhdsa_hash.shake256 ~output_length:P.m
          (randomizer ^ public_key ^ message)
    | `Sha2 ->
        let digest =
          if P.n = 16 then
            Slhdsa_hash.sha256 (randomizer ^ public_key ^ message)
          else Slhdsa_hash.sha512 (randomizer ^ public_key ^ message)
        in
        let seed = randomizer ^ verification_key.pk_seed ^ digest in
        if P.n = 16 then Slhdsa_hash.mgf1_sha256 ~output_length:P.m seed
        else Slhdsa_hash.mgf1_sha512 ~output_length:P.m seed

  let constant_time_equal left right =
    if String.length left <> String.length right then false
    else
      let difference = ref 0 in
      for i = 0 to String.length left - 1 do
        difference :=
          !difference lor
          (Char.code (String.unsafe_get left i)
           lxor Char.code (String.unsafe_get right i))
      done;
      !difference = 0

  let base_w_nibbles message =
    Array.init wots_len1 (fun index ->
        let byte = Char.code (String.unsafe_get message (index / 2)) in
        if index land 1 = 0 then byte lsr 4 else byte land 0x0f)

  let chain_lengths message =
    let result = Array.make wots_len 0 in
    let digits = base_w_nibbles message in
    Array.blit digits 0 result 0 wots_len1;
    let checksum = ref 0 in
    for i = 0 to wots_len1 - 1 do
      checksum := !checksum + (wots_w - 1 - result.(i))
    done;
    let checksum = !checksum lsl 4 in
    result.(wots_len1) <- (checksum lsr 12) land 0x0f;
    result.(wots_len1 + 1) <- (checksum lsr 8) land 0x0f;
    result.(wots_len1 + 2) <- (checksum lsr 4) land 0x0f;
    result

  let rec chain context address value position count =
    if count = 0 || position = wots_w then value
    else
      let address = { address with field2 = position } in
      chain context address (thash context address [ value ]) (position + 1)
        (count - 1)

  let wots_leaf ?capture context base_address leaf_index =
    let wots_address =
      { (with_type 0 base_address) with keypair = leaf_index }
    in
    let public_elements = Array.make wots_len "" in
    for index = 0 to wots_len - 1 do
      let address = { wots_address with field1 = index; field2 = 0 } in
      let secret = prf context (with_type 5 address) in
      (match capture with
       | None -> ()
       | Some (lengths, signature) ->
           signature.(index) <- chain context address secret 0 lengths.(index));
      public_elements.(index) <- chain context address secret 0 (wots_w - 1)
    done;
    let public_key_address = keypair_address 1 wots_address in
    thash context public_key_address (Array.to_list public_elements)

  let wots_public_key_from_signature context base_address message signature =
    let lengths = chain_lengths message in
    let public_elements = Array.make wots_len "" in
    let wots_address = with_type 0 base_address in
    for index = 0 to wots_len - 1 do
      let address = { wots_address with field1 = index; field2 = 0 } in
      public_elements.(index) <-
        chain context address signature.(index) lengths.(index)
          (wots_w - 1 - lengths.(index))
    done;
    public_elements

  let treehash context ~leaf_index ~index_offset ~height ~tree_address gen_leaf =
    (* [authentication] has one slot per level below the root. A leaf index
       outside the tree would blit past it or leave the path zeroed; -1 asks
       for the root alone. *)
    if leaf_index >= 1 lsl height then
      invalid_arg (P.name ^ ": tree hash leaf index outside the tree");
    let stack = Array.make (height + 1) "" in
    let heights = Array.make (height + 1) 0 in
    let offset = ref 0 in
    let authentication = Bytes.make (height * P.n) '\000' in
    for index = 0 to (1 lsl height) - 1 do
      stack.(!offset) <- gen_leaf (index + index_offset);
      heights.(!offset) <- 0;
      incr offset;
      if leaf_index >= 0 && (leaf_index lxor 1) = index then
        Bytes.blit_string stack.(!offset - 1) 0 authentication 0 P.n;
      while !offset >= 2 && heights.(!offset - 1) = heights.(!offset - 2) do
        let node_height = heights.(!offset - 1) in
        let tree_index = index lsr (node_height + 1) in
        let address =
          {
            tree_address with
            field1 = node_height + 1;
            field2 = tree_index + (index_offset lsr (node_height + 1));
          }
        in
        stack.(!offset - 2) <-
          thash context address [ stack.(!offset - 2); stack.(!offset - 1) ];
        decr offset;
        heights.(!offset - 1) <- node_height + 1;
        if
          leaf_index >= 0
          && (((leaf_index lsr heights.(!offset - 1)) lxor 1) = tree_index)
        then
          Bytes.blit_string stack.(!offset - 1) 0 authentication
            (heights.(!offset - 1) * P.n) P.n
      done
    done;
    stack.(0), Bytes.unsafe_to_string authentication

  let compute_root context ~leaf ~leaf_index ~index_offset ~height
      ~authentication ~tree_address =
    let node = ref leaf in
    for level = 0 to height - 1 do
      let sibling = sub authentication (level * P.n) P.n in
      let blocks =
        if ((leaf_index lsr level) land 1) = 0 then [ !node; sibling ]
        else [ sibling; !node ]
      in
      let address =
        {
          tree_address with
          field1 = level + 1;
          field2 =
            (leaf_index lsr (level + 1))
            + (index_offset lsr (level + 1));
        }
      in
      node := thash context address blocks
    done;
    !node

  let message_to_fors_indices message =
    let input = ref 0 in
    let bits = ref 0 in
    let total = ref 0 in
    let mask = (1 lsl P.a) - 1 in
    Array.init P.k (fun _ ->
        while !bits < P.a do
          total :=
            (!total lsl 8)
            + Char.code (String.unsafe_get message !input);
          incr input;
          bits := !bits + 8
        done;
        bits := !bits - P.a;
        (!total lsr !bits) land mask)

  let fors_leaf context base_address index =
    let address =
      { (with_type 6 base_address) with field1 = 0; field2 = index }
    in
    let secret = prf context address in
    thash context { address with typ = 3 } [ secret ]

  let fors_sign context base_address message =
    let indices = message_to_fors_indices message in
    let roots = Array.make P.k "" in
    let signature = Buffer.create fors_signature_size in
    let tree_address = keypair_address 3 base_address in
    for tree = 0 to P.k - 1 do
      let index_offset = tree lsl P.a in
      let selected = indices.(tree) + index_offset in
      let secret_address =
        { tree_address with typ = 6; field1 = 0; field2 = selected }
      in
      Buffer.add_string signature (prf context secret_address);
      let root, authentication =
        treehash context ~leaf_index:indices.(tree) ~index_offset
          ~height:P.a ~tree_address
          (fors_leaf context tree_address)
      in
      roots.(tree) <- root;
      Buffer.add_string signature authentication
    done;
    let public_key_address = keypair_address 4 base_address in
    Buffer.contents signature,
    thash context public_key_address (Array.to_list roots)

  let fors_public_key_from_signature context base_address message signature =
    let indices = message_to_fors_indices message in
    let roots = Array.make P.k "" in
    let position = ref 0 in
    let tree_address = keypair_address 3 base_address in
    for tree = 0 to P.k - 1 do
      let index_offset = tree lsl P.a in
      let selected = indices.(tree) + index_offset in
      let secret = sub signature !position P.n in
      position := !position + P.n;
      let authentication = sub signature !position (P.a * P.n) in
      position := !position + (P.a * P.n);
      let leaf_address =
        { tree_address with field1 = 0; field2 = selected }
      in
      let leaf = thash context leaf_address [ secret ] in
      roots.(tree) <-
        compute_root context ~leaf ~leaf_index:indices.(tree) ~index_offset
          ~height:P.a ~authentication ~tree_address
    done;
    thash context (keypair_address 4 base_address) (Array.to_list roots)

  let merkle_sign context base_address leaf_index message =
    let lengths = chain_lengths message in
    let wots_signature = Array.make wots_len "" in
    let tree_address = subtree_address 2 base_address in
    let root, authentication =
      treehash context ~leaf_index ~index_offset:0 ~height:tree_height
        ~tree_address
        (fun index ->
          if index = leaf_index then
            wots_leaf ~capture:(lengths, wots_signature) context base_address index
          else wots_leaf context base_address index)
    in
    String.concat "" (Array.to_list wots_signature) ^ authentication, root

  let merkle_root context =
    let base_address =
      { zero_address with layer = P.d - 1; typ = 0 }
    in
    let tree_address = subtree_address 2 base_address in
    fst
      (treehash context ~leaf_index:(-1) ~index_offset:0
         ~height:tree_height ~tree_address
         (wots_leaf context base_address))

  let bytes_to_u64 string offset length =
    let result = ref 0L in
    for i = 0 to length - 1 do
      result :=
        Int64.logor (Int64.shift_left !result 8)
          (Int64.of_int (Char.code (String.unsafe_get string (offset + i))))
    done;
    !result

  let low_mask bits =
    if bits = 64 then Int64.minus_one
    else Int64.sub (Int64.shift_left 1L bits) 1L

  let split_message_digest digest =
    let fors_message = sub digest 0 fors_message_bytes in
    let tree =
      Int64.logand
        (bytes_to_u64 digest fors_message_bytes tree_bytes)
        (low_mask tree_bits)
    in
    let leaf =
      Int64.to_int
        (Int64.logand
           (bytes_to_u64 digest (fors_message_bytes + tree_bytes) leaf_bytes)
           (low_mask tree_height))
    in
    fors_message, tree, leaf

  let verification_key_to_octets (key : verification_key) =
    key.pk_seed ^ key.pk_root

  let signing_key_to_octets (key : signing_key) =
    key.sk_seed ^ key.sk_prf ^ verification_key_to_octets key.verification_key

  let signing_key_to_seed (key : signing_key) = key.seed
  let verification_key_of_signing_key (key : signing_key) =
    key.verification_key
  let signature_to_octets signature = signature

  let verification_key_of_octets value =
    if String.length value <> verification_key_size then
      invalid_length "SLH-DSA verification key" verification_key_size value
    else
      Ok
        {
          pk_seed = sub value 0 P.n;
          pk_root = sub value P.n P.n;
        }

  let signature_of_octets value =
    if String.length value <> signature_size then
      invalid_length "SLH-DSA signature" signature_size value
    else Ok value

  let keypair_from_seed seed =
    let sk_seed = sub seed 0 P.n in
    let sk_prf = sub seed P.n P.n in
    let pk_seed = sub seed (2 * P.n) P.n in
    let context = { sk_seed; pk_seed } in
    let pk_root = merkle_root context in
    let verification_key = { pk_seed; pk_root } in
    { sk_seed; sk_prf; verification_key; seed = Some seed }

  let signing_key_of_seed seed =
    if String.length seed <> seed_size then
      invalid_length "SLH-DSA key-generation seed" seed_size seed
    else Ok (keypair_from_seed seed)

  let signing_key_of_octets value =
    if String.length value <> signing_key_size then
      invalid_length "SLH-DSA signing key" signing_key_size value
    else
      let sk_seed = sub value 0 P.n in
      let sk_prf = sub value P.n P.n in
      let pk_seed = sub value (2 * P.n) P.n in
      let pk_root = sub value (3 * P.n) P.n in
      let context = { sk_seed; pk_seed } in
      let expected_root = merkle_root context in
      if not (constant_time_equal pk_root expected_root) then
        Error (Invalid_encoding "SLH-DSA signing-key root is inconsistent")
      else
        Ok
          {
            sk_seed;
            sk_prf;
            verification_key = { pk_seed; pk_root };
            seed = None;
          }

  let require_random operation random length =
    let value = random length in
    if String.length value <> length then
      invalid_arg
        (Format.sprintf "%s.%s: randomness callback returned %d bytes, expected %d"
           P.name operation (String.length value) length);
    value

  let generate ~random () =
    let seed = require_random "generate" random seed_size in
    let signing_key = keypair_from_seed seed in
    signing_key, signing_key.verification_key

  let sign_formatted_with_randomness (key : signing_key) ~formatted_message randomness =
    if String.length randomness <> P.n then
      invalid_length "SLH-DSA per-signature randomness" P.n randomness
    else
      let verification_key = key.verification_key in
      let context = { sk_seed = key.sk_seed; pk_seed = verification_key.pk_seed } in
      let randomizer =
        prf_message key.sk_prf randomness formatted_message
      in
      let digest = hash_message randomizer verification_key formatted_message in
      let fors_message, initial_tree, initial_leaf = split_message_digest digest in
      let fors_address =
        {
          zero_address with
          tree = initial_tree;
          typ = 0;
          keypair = initial_leaf;
        }
      in
      let fors_signature, initial_root =
        fors_sign context fors_address fors_message
      in
      let signature = Buffer.create signature_size in
      Buffer.add_string signature randomizer;
      Buffer.add_string signature fors_signature;
      let root = ref initial_root in
      let tree = ref initial_tree in
      let leaf = ref initial_leaf in
      for layer = 0 to P.d - 1 do
        let base_address =
          {
            zero_address with
            layer;
            tree = !tree;
            typ = 0;
            keypair = !leaf;
          }
        in
        let segment, next_root =
          merkle_sign context base_address !leaf !root
        in
        Buffer.add_string signature segment;
        root := next_root;
        leaf :=
          Int64.to_int
            (Int64.logand !tree (low_mask tree_height));
        tree := Int64.shift_right_logical !tree tree_height
      done;
      Ok (Buffer.contents signature)

  let formatted_prefix context =
    String.make 1 '\000'
    ^ String.make 1 (Char.unsafe_chr (String.length context))
    ^ context

  let sign ?(context = "") ~random key ~message =
    if String.length context > 255 then Error (Context_too_long (String.length context))
    else
      let randomness = require_random "sign" random P.n in
      sign_formatted_with_randomness key
        ~formatted_message:(formatted_prefix context ^ message)
        randomness

  let sign_deterministic ?(context = "") key ~message =
    if String.length context > 255 then Error (Context_too_long (String.length context))
    else
      sign_formatted_with_randomness key
        ~formatted_message:(formatted_prefix context ^ message)
        key.verification_key.pk_seed

  let sign_internal_for_testing key ~formatted_message ~randomness =
    sign_formatted_with_randomness key ~formatted_message randomness

  let verify_formatted (verification_key : verification_key) ~formatted_message signature =
    if String.length signature <> signature_size then false
    else
      let context = { sk_seed = ""; pk_seed = verification_key.pk_seed } in
      let position = ref 0 in
      let take length =
        let value = sub signature !position length in
        position := !position + length;
        value
      in
      let randomizer = take P.n in
      let digest = hash_message randomizer verification_key formatted_message in
      let fors_message, initial_tree, initial_leaf = split_message_digest digest in
      let fors_address =
        {
          zero_address with
          tree = initial_tree;
          typ = 0;
          keypair = initial_leaf;
        }
      in
      let fors_signature = take fors_signature_size in
      let root = ref
          (fors_public_key_from_signature context fors_address fors_message
             fors_signature)
      in
      let tree = ref initial_tree in
      let leaf = ref initial_leaf in
      for layer = 0 to P.d - 1 do
        let base_address =
          {
            zero_address with
            layer;
            tree = !tree;
            typ = 0;
            keypair = !leaf;
          }
        in
        let encoded_wots = take wots_signature_size in
        let wots_signature =
          Array.init wots_len (fun index -> sub encoded_wots (index * P.n) P.n)
        in
        let wots_public_key =
          wots_public_key_from_signature context base_address !root
            wots_signature
        in
        let wots_leaf =
          thash context (keypair_address 1 base_address)
            (Array.to_list wots_public_key)
        in
        let authentication = take (tree_height * P.n) in
        root :=
          compute_root context ~leaf:wots_leaf ~leaf_index:!leaf
            ~index_offset:0 ~height:tree_height ~authentication
            ~tree_address:(subtree_address 2 base_address);
        leaf :=
          Int64.to_int
            (Int64.logand !tree (low_mask tree_height));
        tree := Int64.shift_right_logical !tree tree_height
      done;
      constant_time_equal !root verification_key.pk_root

  let verify ?(context = "") verification_key ~message signature =
    if String.length context > 255 then false
    else
      verify_formatted verification_key
        ~formatted_message:(formatted_prefix context ^ message)
        signature

  let verify_internal_for_testing verification_key ~formatted_message signature =
    verify_formatted verification_key ~formatted_message signature

  let fors_tree_for_testing ~sk_seed ~pk_seed ~leaf_index =
    let context : hash_context = { sk_seed; pk_seed } in
    let tree_address = keypair_address 3 zero_address in
    treehash context ~leaf_index ~index_offset:0 ~height:P.a ~tree_address
      (fors_leaf context tree_address)
end

module Sha2_128s = Make (struct
  let name = "Slhdsa_sha2_128s"
  let hash = `Sha2
  let n = 16
  let h = 63
  let d = 7
  let a = 12
  let k = 14
  let m = 30
end)

module Sha2_128f = Make (struct
  let name = "Slhdsa_sha2_128f"
  let hash = `Sha2
  let n = 16
  let h = 66
  let d = 22
  let a = 6
  let k = 33
  let m = 34
end)

module Sha2_192s = Make (struct
  let name = "Slhdsa_sha2_192s"
  let hash = `Sha2
  let n = 24
  let h = 63
  let d = 7
  let a = 14
  let k = 17
  let m = 39
end)

module Sha2_192f = Make (struct
  let name = "Slhdsa_sha2_192f"
  let hash = `Sha2
  let n = 24
  let h = 66
  let d = 22
  let a = 8
  let k = 33
  let m = 42
end)

module Sha2_256s = Make (struct
  let name = "Slhdsa_sha2_256s"
  let hash = `Sha2
  let n = 32
  let h = 64
  let d = 8
  let a = 14
  let k = 22
  let m = 47
end)

module Sha2_256f = Make (struct
  let name = "Slhdsa_sha2_256f"
  let hash = `Sha2
  let n = 32
  let h = 68
  let d = 17
  let a = 9
  let k = 35
  let m = 49
end)

module Shake_128s = Make (struct
  let name = "Slhdsa_shake_128s"
  let hash = `Shake
  let n = 16
  let h = 63
  let d = 7
  let a = 12
  let k = 14
  let m = 30
end)

module Shake_128f = Make (struct
  let name = "Slhdsa_shake_128f"
  let hash = `Shake
  let n = 16
  let h = 66
  let d = 22
  let a = 6
  let k = 33
  let m = 34
end)

module Shake_192s = Make (struct
  let name = "Slhdsa_shake_192s"
  let hash = `Shake
  let n = 24
  let h = 63
  let d = 7
  let a = 14
  let k = 17
  let m = 39
end)

module Shake_192f = Make (struct
  let name = "Slhdsa_shake_192f"
  let hash = `Shake
  let n = 24
  let h = 66
  let d = 22
  let a = 8
  let k = 33
  let m = 42
end)

module Shake_256s = Make (struct
  let name = "Slhdsa_shake_256s"
  let hash = `Shake
  let n = 32
  let h = 64
  let d = 8
  let a = 14
  let k = 22
  let m = 47
end)

module Shake_256f = Make (struct
  let name = "Slhdsa_shake_256f"
  let hash = `Shake
  let n = 32
  let h = 68
  let d = 17
  let a = 9
  let k = 35
  let m = 49
end)
