open! Core

let utf_decode n i =
  if Uchar.int_is_scalar i
  then Uchar.of_scalar_exn i |> Stdlib.Uchar.utf_decode n
  else Stdlib.Uchar.utf_decode_invalid n
;;

let[@inline] not_in_x80_to_xBF b = b lsr 6 <> 0b10
let[@inline] not_in_xA0_to_xBF b = b lsr 5 <> 0b101
let[@inline] not_in_x80_to_x9F b = b lsr 5 <> 0b100
let[@inline] not_in_x90_to_xBF b = b < 0x90 || 0xBF < b
let[@inline] not_in_x80_to_x8F b = b lsr 4 <> 0x8
let[@inline] utf_8_uchar_2 b0 b1 = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F)

let[@inline] utf_8_uchar_3 b0 b1 b2 =
  ((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F)
;;

let[@inline] utf_8_uchar_4 b0 b1 b2 b3 =
  ((b0 land 0x07) lsl 18)
  lor ((b1 land 0x3F) lsl 12)
  lor ((b2 land 0x3F) lsl 6)
  lor (b3 land 0x3F)
;;

(* Copied from stdlib, modified as to not check the first char *)
let utf8 (t @ local) ~pos:i ~len ~unsafe_get:get =
  let t0 = get t i in
  let dec_ret = utf_decode in
  let dec_invalid = Stdlib.Uchar.utf_decode_invalid in
  let max = len - 1 in
  match Char.unsafe_of_int t0 with
  (* See The Unicode Standard, Table 3.7 *)
  | '\x00' .. '\x7F' -> dec_ret 1 t0
  | '\xC2' .. '\xDF' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x80_to_xBF t1 then dec_invalid 1 else dec_ret 2 (utf_8_uchar_2 t0 t1))
  | '\xE0' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_xA0_to_xBF t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else dec_ret 3 (utf_8_uchar_3 t0 t1 t2))))
  | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x80_to_xBF t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else dec_ret 3 (utf_8_uchar_3 t0 t1 t2))))
  | '\xED' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x80_to_x9F t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else dec_ret 3 (utf_8_uchar_3 t0 t1 t2))))
  | '\xF0' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x90_to_xBF t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else (
            let i = i + 1 in
            if i > max
            then dec_invalid 3
            else (
              let t3 = get t i in
              if not_in_x80_to_xBF t3
              then dec_invalid 3
              else dec_ret 4 (utf_8_uchar_4 t0 t1 t2 t3))))))
  | '\xF1' .. '\xF3' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x80_to_xBF t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else (
            let i = i + 1 in
            if i > max
            then dec_invalid 3
            else (
              let t3 = get t i in
              if not_in_x80_to_xBF t3
              then dec_invalid 3
              else dec_ret 4 (utf_8_uchar_4 t0 t1 t2 t3))))))
  | '\xF4' ->
    let i = i + 1 in
    if i > max
    then dec_invalid 1
    else (
      let t1 = get t i in
      if not_in_x80_to_x8F t1
      then dec_invalid 1
      else (
        let i = i + 1 in
        if i > max
        then dec_invalid 2
        else (
          let t2 = get t i in
          if not_in_x80_to_xBF t2
          then dec_invalid 2
          else (
            let i = i + 1 in
            if i > max
            then dec_invalid 3
            else (
              let t3 = get t i in
              if not_in_x80_to_xBF t3
              then dec_invalid 3
              else dec_ret 4 (utf_8_uchar_4 t0 t1 t2 t3))))))
  | _ -> dec_invalid 1
;;

let[@inline] utf16 (t @ local) ~pos ~len ~unsafe_get =
  let available_len = len - pos in
  if available_len < 2
  then Stdlib.Uchar.utf_decode_invalid available_len
  else (
    let char = unsafe_get t pos in
    if char < 0xd800 || char >= 0xe000
    then utf_decode 2 char
    else if char > 0xdbff
    then Stdlib.Uchar.utf_decode_invalid 2
    else if available_len < 4
    then Stdlib.Uchar.utf_decode_invalid available_len
    else (
      let char2 = unsafe_get t (pos + 2) in
      if char2 < 0xdc00 || char2 > 0xdfff
      then Stdlib.Uchar.utf_decode_invalid 2
      else (
        let char = ((char - 0xd800) lsl 10) + (char2 - 0xdc00) + 0x10000 in
        utf_decode 4 char)))
;;

let[@inline] utf32 (t @ local) ~pos ~len ~unsafe_get =
  let available_len = len - pos in
  if available_len < 4
  then Stdlib.Uchar.utf_decode_invalid available_len
  else (
    let char = unsafe_get t pos in
    match Int32.to_int char with
    | None -> Stdlib.Uchar.utf_decode_invalid 4
    | Some char -> utf_decode 4 char)
;;

let%expect_test "UTF8 valid" =
  Quickcheck.test Uchar.quickcheck_generator ~f:(fun uchar ->
    let string = Uchar.Utf8.to_string uchar in
    let uchar' =
      utf8 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        String.unsafe_get s i |> Char.to_int)
      |> Uchar.Decode_result.uchar_exn
    in
    assert (Uchar.equal uchar uchar'))
;;

let%expect_test "UTF8 any" =
  Quickcheck.test String.gen_nonempty ~f:(fun string ->
    let reference = String.Utf8.get_unchecked string ~byte_pos:0 in
    let actual =
      utf8 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        String.unsafe_get s i |> Char.to_int)
    in
    assert (Uchar.Decode_result.equal reference actual))
;;

let make_16_be = if Sys.big_endian then Fn.id else Int.bswap16
let make_16_le = if Sys.big_endian then Int.bswap16 else Fn.id

let%expect_test "UTF16-BE valid" =
  Quickcheck.test Uchar.quickcheck_generator ~f:(fun uchar ->
    let string = Uchar.Utf16be.to_string uchar in
    let uchar' =
      utf16 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        Bytes.unsafe_get_int16 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_16_be)
      |> Uchar.Decode_result.uchar_exn
    in
    assert (Uchar.equal uchar uchar'))
;;

let%expect_test "UTF16-BE any" =
  Quickcheck.test String.gen_nonempty ~f:(fun string ->
    let reference = String.Utf16be.get_unchecked string ~byte_pos:0 in
    let actual =
      utf16 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        Bytes.unsafe_get_int16 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_16_be)
    in
    assert (Uchar.Decode_result.equal reference actual))
;;

let%expect_test "UTF16-LE valid" =
  Quickcheck.test Uchar.quickcheck_generator ~f:(fun uchar ->
    let string = Uchar.Utf16le.to_string uchar in
    let uchar' =
      utf16 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        Bytes.unsafe_get_int16 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_16_le)
      |> Uchar.Decode_result.uchar_exn
    in
    assert (Uchar.equal uchar uchar'))
;;

let%expect_test "UTF16-LE any" =
  Quickcheck.test String.gen_nonempty ~f:(fun string ->
    let reference = String.Utf16le.get_unchecked string ~byte_pos:0 in
    let actual =
      utf16 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i ->
        Bytes.unsafe_get_int16 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_16_le)
    in
    assert (Uchar.Decode_result.equal reference actual))
;;

let make_32_be = if Sys.big_endian then Fn.id else Int32.bswap32
let make_32_le = if Sys.big_endian then Int32.bswap32 else Fn.id

let%expect_test "UTF32-BE valid" =
  Quickcheck.test Uchar.quickcheck_generator ~f:(fun uchar ->
    let string = Uchar.Utf32be.to_string uchar in
    let uchar' =
      utf32 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i -> exclave_
        Bytes.unsafe_get_int32 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_32_be)
      |> Uchar.Decode_result.uchar_exn
    in
    assert (Uchar.equal uchar uchar'))
;;

let%expect_test "UTF32-BE any" =
  Quickcheck.test String.gen_nonempty ~f:(fun string ->
    let reference = String.Utf32be.get_unchecked string ~byte_pos:0 in
    let actual =
      utf32 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i -> exclave_
        Bytes.unsafe_get_int32 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_32_be)
    in
    assert (Uchar.Decode_result.equal reference actual))
;;

let%expect_test "UTF32-LE valid" =
  Quickcheck.test Uchar.quickcheck_generator ~f:(fun uchar ->
    let string = Uchar.Utf32le.to_string uchar in
    let uchar' =
      utf32 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i -> exclave_
        Bytes.unsafe_get_int32 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_32_le)
      |> Uchar.Decode_result.uchar_exn
    in
    assert (Uchar.equal uchar uchar'))
;;

let%expect_test "UTF32-LE any" =
  Quickcheck.test String.gen_nonempty ~f:(fun string ->
    let reference = String.Utf32le.get_unchecked string ~byte_pos:0 in
    let actual =
      utf32 string ~pos:0 ~len:(String.length string) ~unsafe_get:(fun s i -> exclave_
        Bytes.unsafe_get_int32 (Bytes.unsafe_of_string_promise_no_mutation s) i
        |> make_32_le)
    in
    assert (Uchar.Decode_result.equal reference actual))
;;
