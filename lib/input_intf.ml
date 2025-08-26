open! Core

module type S = sig
  module Char : sig
    type t
  end

  type t

  module Index : sig
    type t
  end

  val end_ : t @ local -> Index.t or_null
  val next : t @ local -> (Index.t * Char.t) or_null

  module Unsafe : sig
    val get : t @ local -> Index.t @ local -> Char.t
  end
end
