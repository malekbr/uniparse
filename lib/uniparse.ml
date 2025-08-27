open! Core

(* Idea: add a run function that returns no result, to be used by
   consumed *)

module Encoding = struct
  type _ t =
    | Byte : [ `Byte ] t
    | Utf8 : [ `Unicode ] t
    | Utf16_be : [ `Unicode ] t
    | Utf16_le : [ `Unicode ] t
    | Utf32_be : [ `Unicode ] t
    | Utf32_le : [ `Unicode ] t
  [@@deriving sexp_of]

  type packed = Packed : _ t -> packed
end

module With_encoding = struct
  type ('a, 'encoding) t =
    { encoding : 'encoding Encoding.t
    ; value : 'a
    }

  let lift_string t ~(target_encoding : [ `Unicode ] Encoding.t) =
    let of_array array =
      match target_encoding with
      | Utf8 -> String.Utf8.of_array array |> String.Utf8.to_string
      | Utf16_be -> String.Utf16be.of_array array |> String.Utf16be.to_string
      | Utf16_le -> String.Utf16le.of_array array |> String.Utf16le.to_string
      | Utf32_be -> String.Utf32be.of_array array |> String.Utf32be.to_string
      | Utf32_le -> String.Utf32le.of_array array |> String.Utf32le.to_string
    in
    match t.encoding, target_encoding with
    | Utf8, Utf8
    | Utf16_be, Utf16_be
    | Utf16_le, Utf16_le
    | Utf32_be, Utf32_be
    | Utf32_le, Utf32_le -> t.value
    | Utf8, _ -> String.Utf8.of_string t.value |> String.Utf8.to_array |> of_array
    | Utf16_be, _ ->
      String.Utf16be.of_string t.value |> String.Utf16be.to_array |> of_array
    | Utf16_le, _ ->
      String.Utf16le.of_string t.value |> String.Utf16le.to_array |> of_array
    | Utf32_be, _ ->
      String.Utf32be.of_string t.value |> String.Utf32be.to_array |> of_array
    | Utf32_le, _ ->
      String.Utf32le.of_string t.value |> String.Utf32le.to_array |> of_array
  ;;
end

module Get_uchar = struct
  type ('base, _) t =
    | Get :
        ('base @ local -> pos:int -> len:int -> Uchar.Decode_result.t)
        -> ('base, [ `Unicode ]) t
    | Undef : ('base, [ `Byte ]) t
end

module Parse_result = struct
  type ('a : value_or_null) t =
    | Parsed of
        { value : 'a @@ global
        ; next_pos : int
        }
    | Failed of
        { reason : string @@ global
        ; call_pos : Source_code_position.t @@ global
        }
end

module Sub_target = struct
  type 'a t =
    | String : string t
    | Bytes : bytes t
    | Bigstring : Bigstring.t t
end

type ('base, 'target, 'enc) sub =
  'base @ local
  -> 'target Sub_target.t
  -> pos:int
  -> len:int
  -> ('target, 'enc) With_encoding.t

type ('a : value_or_null, 'char) t =
  { run :
      'base.
      'base @ local
      -> pos:int
      -> len:int
      -> unsafe_get_char:('base @ local -> int -> char) @ local
      -> unsafe_get_uchar:('base, 'char) Get_uchar.t @ local
      -> sub:('target. ('base, 'target, 'char) sub) @ local
      -> 'a Parse_result.t @ local
  }
[@@unboxed]

let fail ~(call_pos : [%call_pos]) reason =
  { run =
      (fun _base ~pos:_ ~len:_ ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        Failed { reason; call_pos })
  }
;;

let return value =
  { run =
      (fun _base ~pos ~len:_ ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        Parsed { value; next_pos = pos })
  }
;;

let bind t ~f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          let next = f value in
          exclave_
          next.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
        | Failed { reason; call_pos } -> Failed { reason; call_pos })
  }
;;

let map t ~f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> Parsed { value = f value; next_pos }
        | Failed { reason; call_pos } -> Failed { reason; call_pos })
  }
;;

let map = `Custom map

include functor Monad.Make2

let both t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = v1; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value = v2; next_pos } ->
             exclave_ Parsed { value = v1, v2; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

module Nary_monadic_operators = struct
  (*$
    open! Core

    (* dune doesn't support setting the formatter yet, so we have to
       do this ugly trick. *)
    let () = print_endline ""
    let () = print_endline {|  [@@@ocamlformat "disable"]|}
    let () = print_endline ""

    let make_run n ~content =
      [%string
        {| (match t%{n#Int}.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v%{n#Int}; next_pos } ->
          %{content}
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })|}]
    ;;

    let make_t ~content =
      [%string
        {| { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> %{content}) }|}]
    ;;

    let make_function n ~name ~content =
      let arguments =
        List.init n ~f:(fun i -> [%string {|t%{i#Int}|}]) |> String.concat ~sep:" "
      in
      let f_arguments =
        List.init n ~f:(fun i -> [%string {|v%{i#Int}|}]) |> String.concat ~sep:" "
      in
      let content = content ~arguments:f_arguments in
      let content =
        Sequence.range ~stride:(-1) ~start:`exclusive ~stop:`inclusive n 0
        |> Sequence.fold ~init:content ~f:(fun content i -> make_run i ~content)
      in
      let content = make_t ~content in
      [%string {|  let %{name}%{n#Int} %{arguments} ~f = %{content}|}]
      ^ "\n"
    ;;

    let () =
      for i = 2 to 16 do
        make_function i ~name:"map" ~content:(fun ~arguments ->
            [%string "exclave_ Parsed { value = f %{arguments}; next_pos }"])
        |> print_endline
      done
    ;;

    let () =
      for i = 2 to 16 do
        make_function i ~name:"bind" ~content:(fun ~arguments ->
            [%string
              {|
        (match (f %{arguments}).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })|}])
        |> print_endline
      done;;

    let () = print_string "  "
  *)
  [@@@ocamlformat "disable"]

  let map2 t0 t1 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
          exclave_ Parsed { value = f v0 v1; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map3 t0 t1 t2 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map4 t0 t1 t2 t3 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map5 t0 t1 t2 t3 t4 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map6 t0 t1 t2 t3 t4 t5 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map7 t0 t1 t2 t3 t4 t5 t6 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map8 t0 t1 t2 t3 t4 t5 t6 t7 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map9 t0 t1 t2 t3 t4 t5 t6 t7 t8 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map10 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map11 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map13 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map14 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map15 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
           (match t15.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v15; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind2 t0 t1 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
          
        (match (f v0 v1).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind3 t0 t1 t2 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
          
        (match (f v0 v1 v2).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind4 t0 t1 t2 t3 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
          
        (match (f v0 v1 v2 v3).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind5 t0 t1 t2 t3 t4 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind6 t0 t1 t2 t3 t4 t5 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind7 t0 t1 t2 t3 t4 t5 t6 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind8 t0 t1 t2 t3 t4 t5 t6 t7 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind9 t0 t1 t2 t3 t4 t5 t6 t7 t8 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind10 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind11 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind13 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind14 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind15 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
           (match t15.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v15; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  (*$*)

  [@@@ocamlformat "enable"]
end

include Nary_monadic_operators

module Let_syntax = struct
  include Let_syntax

  module Let_syntax = struct
    open struct
      let both_ = both
    end

    include Let_syntax

    let both = both_

    include Nary_monadic_operators
  end
end

let satisfy_ascii ~(call_pos : [%call_pos]) f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ -> exclave_
        if pos < len
        then (
          let char = unsafe_get_char base pos in
          if f char
          then Parsed { value = char; next_pos = pos + 1 }
          else Failed { reason = "satisfy"; call_pos })
        else Failed { reason = "satisfy reached end"; call_pos })
  }
;;

let satisfy ~(call_pos : [%call_pos]) f =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ -> exclave_
        if pos < len
        then (
          let uchar = unsafe_get_uchar base ~pos ~len in
          let value = Uchar.Decode_result.uchar_or_replacement_char uchar in
          if f value
          then Parsed { value; next_pos = pos + Uchar.Decode_result.bytes_consumed uchar }
          else Failed { reason = "usatisfy"; call_pos })
        else Failed { reason = "usatisfy reached end"; call_pos })
  }
;;

let rec loop_choices
  ~call_pos
  ~failure_message
  choices
  base
  ~pos
  ~len
  ~unsafe_get_char
  ~unsafe_get_uchar
  ~(sub : 'target. ('base, 'target, _) sub)
  : _ Parse_result.t @ local
  =
  match choices with
  | [] -> exclave_ Failed { reason = failure_message; call_pos }
  | choice :: choices ->
    (match choice.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
     | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
     | Failed _ ->
       exclave_
       loop_choices
         ~call_pos
         ~failure_message
         choices
         base
         ~pos
         ~len
         ~unsafe_get_char
         ~unsafe_get_uchar
         ~sub)
;;

let choose ~(call_pos : [%call_pos]) ?(failure_message = "choose") choices =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> exclave_
        loop_choices
          ~call_pos
          ~failure_message
          choices
          base
          ~pos
          ~len
          ~unsafe_get_char
          ~unsafe_get_uchar
          ~sub)
  }
;;

let skip_bytes ~(call_pos : [%call_pos]) ?(on_overflow = `Fail "skip_bytes overflow") n =
  { run =
      (fun _base ~pos ~len ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ -> exclave_
        let next_pos = pos + n in
        if next_pos > len
        then (
          match on_overflow with
          | `Fail reason -> Failed { reason; call_pos }
          | `Truncate -> Parsed { value = (); next_pos = len })
        else Parsed { value = (); next_pos })
  }
;;

let skip_chars ~(call_pos : [%call_pos]) ?(on_overflow = `Fail "skip_chars overflow") n =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base n ~pos ~len ~unsafe_get_uchar : _ Parse_result.t @ local =
          if n = 0
          then exclave_ Parsed { value = (); next_pos = pos }
          else if pos < len
          then (
            let uchar = unsafe_get_uchar base ~pos ~len in
            exclave_
            loop
              base
              (n - 1)
              ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
              ~len
              ~unsafe_get_uchar)
          else (
            match on_overflow with
            | `Fail reason -> exclave_ Failed { reason; call_pos }
            | `Truncate -> exclave_ Parsed { value = (); next_pos = len })
        in
        exclave_ loop base n ~pos ~len ~unsafe_get_uchar)
  }
;;

let skip_while_ascii f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_char : _ Parse_result.t @ local =
          if pos < len
          then (
            let char = unsafe_get_char base pos in
            if f char
            then exclave_ loop base ~pos:(pos + 1) ~len ~unsafe_get_char
            else exclave_ Parsed { value = (); next_pos = pos })
          else exclave_ Parsed { value = (); next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_char)
  }
;;

let skip_while f =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_uchar : _ Parse_result.t @ local =
          if pos < len
          then (
            let uchar = unsafe_get_uchar base ~pos ~len in
            if f (Uchar.Decode_result.uchar_or_replacement_char uchar)
            then
              exclave_
              loop
                base
                ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
                ~len
                ~unsafe_get_uchar
            else exclave_ Parsed { value = (); next_pos = pos })
          else exclave_ Parsed { value = (); next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_uchar)
  }
;;

let fold_while ~f ~init =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_uchar ~init : _ Parse_result.t @ local =
          if pos < len
          then (
            let uchar = unsafe_get_uchar base ~pos ~len in
            match f init (Uchar.Decode_result.uchar_or_replacement_char uchar) with
            | This init ->
              exclave_
              loop
                base
                ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
                ~len
                ~unsafe_get_uchar
                ~init
            | Null -> exclave_ Parsed { value = init; next_pos = pos })
          else exclave_ Parsed { value = init; next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_uchar ~init)
  }
;;

let nonempty ~(call_pos : [%call_pos]) t =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          if next_pos > pos
          then exclave_ Parsed { value; next_pos }
          else exclave_ Failed { reason = "nonempty"; call_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let consumed' t ~target =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = _; next_pos } ->
          exclave_ Parsed { value = sub base target ~pos ~len:(next_pos - pos); next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let consumed t = consumed' t ~target:String

let fix f =
  let rec t =
    { run =
        (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> exclave_
          (f t).run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub)
    }
  in
  t
;;

let end_of_input ~(call_pos : [%call_pos]) () =
  { run =
      (fun _base ~pos ~len ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        if pos = len
        then exclave_ Parsed { value = (); next_pos = pos }
        else exclave_ Failed { reason = "end_of_input"; call_pos })
  }
;;

let string ~(call_pos : [%call_pos]) s =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ ->
        let string_len = String.length s in
        if len < pos + string_len
        then exclave_ Failed { reason = "string"; call_pos }
        else (
          let rec equal i =
            if i = string_len
            then true
            else if Char.equal (String.unsafe_get s i) (unsafe_get_char base (pos + i))
            then equal (i + 1)
            else false
          in
          if equal 0
          then exclave_ Parsed { value = s; next_pos = pos + string_len }
          else exclave_ Failed { reason = "string"; call_pos }))
  }
;;

let optional (type a : value_or_null) t ~(default : a) ~return =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value = return value; next_pos }
        | Failed _ -> exclave_ Parsed { value = default; next_pos = pos })
  }
;;

let rec reverse_local_list_of_globals_into_global_list (list @ local) ~acc =
  match list with
  | [] -> acc
  | { global } :: rest ->
    reverse_local_list_of_globals_into_global_list rest ~acc:(global :: acc)
;;

let rec many_loop
  t
  base
  ~pos
  ~len
  ~unsafe_get_char
  ~unsafe_get_uchar
  ~(sub : 'target. ('base, 'target, _) sub)
  ~(acc @ local)
  =
  match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
  | Parsed { value; next_pos } ->
    exclave_
    many_loop
      t
      base
      ~pos:next_pos
      ~len
      ~unsafe_get_char
      ~unsafe_get_uchar
      ~sub
      ~acc:({ global = value } :: acc)
  | Failed _ ->
    exclave_ ~pos, { global = reverse_local_list_of_globals_into_global_list acc ~acc:[] }
;;

let ( <* ) t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value = _; next_pos } -> exclave_ Parsed { value; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let ( *> ) t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = _; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let many t =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        let ~pos, { global = value } =
          many_loop t base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ~acc:[]
        in
        exclave_ Parsed { value; next_pos = pos })
  }
;;

let many1 ~(call_pos : [%call_pos]) t = nonempty ~call_pos (many t)

let sep_by ~(call_pos : [%call_pos]) t ~sep =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = hd; next_pos } ->
          (match
             (many (sep *> t)).run
               base
               ~pos:next_pos
               ~len
               ~unsafe_get_char
               ~unsafe_get_uchar
               ~sub
           with
           | Parsed { value = tl; next_pos } ->
             exclave_ Parsed { value = hd :: tl; next_pos }
           | Failed _ -> exclave_ Parsed { value = [ hd ]; next_pos })
        | Failed _ -> exclave_ Parsed { value = []; next_pos = pos })
  }
;;

let sep_by1 ~(call_pos : [%call_pos]) t ~sep =
  nonempty ~call_pos (sep_by ~call_pos t ~sep)
;;

let parse_generic
  ~(call_pos : [%call_pos])
  t
  base
  ~pos
  ~len
  ~consume
  ~unsafe_get_char
  ~unsafe_get_uchar
  ~(sub : 'target. ('base, 'target, _) sub)
  =
  match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
  | Parsed { value; next_pos } ->
    (match next_pos < len, consume with
     | _, `Prefix | false, `All -> Ok value
     | true, `All ->
       error_s
         [%message
           "Parse error, consume is `All but not all of the input was consumed"
             (call_pos : Source_code_position.t)])
  | Failed { reason; call_pos } ->
    error_s [%message reason (call_pos : Source_code_position.t)]
;;

let parse_string
  (type encoding)
  ~(call_pos : [%call_pos])
  t
  ?(pos = 0)
  ?len
  s
  ~consume
  ~(encoding : encoding Encoding.t)
  =
  let string_len = String.length s in
  let len =
    match len with
    | None -> string_len
    | Some len -> if len > string_len then string_len else len
  in
  let unsafe_get_uchar : (string, encoding) Get_uchar.t =
    let guard_len uchar_decode ~pos ~len =
      let available = len - pos in
      if Uchar.Decode_result.bytes_consumed uchar_decode > available
      then Stdlib.Uchar.utf_decode_invalid available
      else uchar_decode
    in
    match encoding with
    | Byte -> Get_uchar.Undef
    | Utf8 ->
      Get_uchar.Get
        (fun s ~pos ~len ->
          String.Utf8.get_unchecked s ~byte_pos:pos |> guard_len ~pos ~len)
    | Utf16_be ->
      Get_uchar.Get
        (fun s ~pos ~len ->
          String.Utf16be.get_unchecked s ~byte_pos:pos |> guard_len ~pos ~len)
    | Utf16_le ->
      Get_uchar.Get
        (fun s ~pos ~len ->
          String.Utf16le.get_unchecked s ~byte_pos:pos |> guard_len ~pos ~len)
    | Utf32_be ->
      Get_uchar.Get
        (fun s ~pos ~len ->
          String.Utf32be.get_unchecked s ~byte_pos:pos |> guard_len ~pos ~len)
    | Utf32_le ->
      Get_uchar.Get
        (fun s ~pos ~len ->
          String.Utf32le.get_unchecked s ~byte_pos:pos |> guard_len ~pos ~len)
  in
  let sub (type target) (base : string @ local) (target : target Sub_target.t) ~pos ~len =
    let value : target =
      match target with
      | String ->
        Bytes.unsafe_to_string
          ~no_mutation_while_string_reachable:(Bytes.From_string.sub base ~pos ~len)
      | Bytes -> Bytes.From_string.sub base ~pos ~len
      | Bigstring -> Bigstring.From_string.sub base ~pos ~len
    in
    { With_encoding.encoding; value }
  in
  parse_generic
    ~call_pos
    t
    s
    ~pos
    ~len
    ~consume
    ~unsafe_get_char:String.unsafe_get
    ~unsafe_get_uchar
    ~sub
;;

let parse_bytes
  (type encoding)
  ~(call_pos : [%call_pos])
  t
  ?(pos = 0)
  ?len
  bytes
  ~consume
  ~(encoding : encoding Encoding.t)
  =
  let bytes_len = Bytes.length bytes in
  let len =
    match len with
    | None -> bytes_len
    | Some len -> if len > bytes_len then bytes_len else len
  in
  let unsafe_get_uchar : (bytes, encoding) Get_uchar.t =
    match encoding with
    | Byte -> Get_uchar.Undef
    | Utf8 ->
      Get_uchar.Get
        (fun bytes ~pos ~len ->
          Unicode_helpers.utf8 bytes ~pos ~len ~unsafe_get:(fun bytes pos ->
            Bytes.unsafe_get bytes pos |> Char.to_int))
    | Utf16_be ->
      Get_uchar.Get
        (fun bytes ~pos ~len ->
          Unicode_helpers.utf16 bytes ~pos ~len ~unsafe_get:(fun bytes pos ->
            Bytes.unsafe_get_int16 bytes pos |> Unicode_helpers.make_16_be))
    | Utf16_le ->
      Get_uchar.Get
        (fun bytes ~pos ~len ->
          Unicode_helpers.utf16 bytes ~pos ~len ~unsafe_get:(fun bytes pos ->
            Bytes.unsafe_get_int16 bytes pos |> Unicode_helpers.make_16_le))
    | Utf32_be ->
      Get_uchar.Get
        (fun bytes ~pos ~len ->
          Unicode_helpers.utf32 bytes ~pos ~len ~unsafe_get:(fun bytes pos -> exclave_
            Bytes.unsafe_get_int32 bytes pos |> Unicode_helpers.make_32_be))
    | Utf32_le ->
      Get_uchar.Get
        (fun bytes ~pos ~len ->
          Unicode_helpers.utf32 bytes ~pos ~len ~unsafe_get:(fun bytes pos -> exclave_
            Bytes.unsafe_get_int32 bytes pos |> Unicode_helpers.make_32_le))
  in
  let sub (type target) (base : bytes @ local) (target : target Sub_target.t) ~pos ~len =
    let value : target =
      match target with
      | String -> Bytes.To_string.sub base ~pos ~len
      | Bytes -> Bytes.sub base ~pos ~len
      | Bigstring -> Bigstring.From_bytes.sub base ~pos ~len
    in
    { With_encoding.encoding; value }
  in
  parse_generic
    ~call_pos
    t
    bytes
    ~pos
    ~len
    ~consume
    ~unsafe_get_char:Bytes.unsafe_get
    ~unsafe_get_uchar
    ~sub
;;

let parse_bigstring
  (type encoding)
  ~(call_pos : [%call_pos])
  t
  ?(pos = 0)
  ?len
  bigstring
  ~consume
  ~(encoding : encoding Encoding.t)
  =
  let bigstring_len = Bigstring.length bigstring in
  let len =
    match len with
    | None -> bigstring_len
    | Some len -> if len > bigstring_len then bigstring_len else len
  in
  let unsafe_get_uchar : (bigstring, encoding) Get_uchar.t =
    match encoding with
    | Byte -> Get_uchar.Undef
    | Utf8 ->
      Get_uchar.Get
        (fun bigstring ~pos ~len ->
          Unicode_helpers.utf8 bigstring ~pos ~len ~unsafe_get:(fun bigstring pos ->
            Bigstring.get_uint8 bigstring ~pos))
    | Utf16_be ->
      Get_uchar.Get
        (fun bigstring ~pos ~len ->
          Unicode_helpers.utf16 bigstring ~pos ~len ~unsafe_get:(fun bigstring pos ->
            Bigstring.get_uint16_be bigstring ~pos))
    | Utf16_le ->
      Get_uchar.Get
        (fun bigstring ~pos ~len ->
          Unicode_helpers.utf16 bigstring ~pos ~len ~unsafe_get:(fun bigstring pos ->
            Bigstring.get_uint16_le bigstring ~pos))
    | Utf32_be ->
      Get_uchar.Get
        (fun bigstring ~pos ~len ->
          Unicode_helpers.utf32 bigstring ~pos ~len ~unsafe_get:(fun bigstring pos ->
            Bigstring.get_int32_t_be bigstring ~pos))
    | Utf32_le ->
      Get_uchar.Get
        (fun bigstring ~pos ~len ->
          Unicode_helpers.utf32 bigstring ~pos ~len ~unsafe_get:(fun bigstring pos ->
            Bigstring.get_int32_t_le bigstring ~pos))
  in
  let sub
    (type target)
    (base : bigstring @ local)
    (target : target Sub_target.t)
    ~pos
    ~len
    =
    let value : target =
      match target with
      | String -> Bigstring.To_string.sub base ~pos ~len
      | Bytes -> Bigstring.To_bytes.sub base ~pos ~len
      | Bigstring -> Bigstring.sub base ~pos ~len
    in
    { With_encoding.encoding; value }
  in
  parse_generic
    ~call_pos
    t
    bigstring
    ~pos
    ~len
    ~consume
    ~unsafe_get_char:Bigstring.unsafe_get
    ~unsafe_get_uchar
    ~sub
;;
