/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.data.buffer
import Mathlib.Lean3Lib.system.random
 

universes l 

namespace Mathlib

inductive io.error 
where
| other : string → io.error
| sys : ℕ → io.error

inductive io.mode 
where
| read : io.mode
| write : io.mode
| read_write : io.mode
| append : io.mode

inductive io.process.stdio 
where
| piped : io.process.stdio
| inherit : io.process.stdio
| null : io.process.stdio

/- Command name. -/

structure io.process.spawn_args 
where
  cmd : string
  args : List string
  stdin : io.process.stdio
  stdout : io.process.stdio
  stderr : io.process.stdio
  cwd : Option string
  env : List (string × Option string)

/- Arguments for the process -/

/- Configuration for the process' stdin handle. -/

/- Configuration for the process' stdout handle. -/

/- Configuration for the process' stderr handle. -/

/- Working directory for the process. -/

/- Environment variables for the process. -/

class monad_io (m : Type → Type → Type) 
where
  monad : (e : Type) → Monad (m e)
  catch : (e₁ e₂ α : Type) → m e₁ α → (e₁ → m e₂ α) → m e₂ α
  fail : (e α : Type) → e → m e α
  iterate : (e α : Type) → α → (α → m e (Option α)) → m e α
  handle : Type

-- TODO(Leo): use monad_except after it is merged

-- Primitive Types

class monad_io_terminal (m : Type → Type → Type) 
where
  put_str : string → m io.error Unit
  get_line : m io.error string
  cmdline_args : List string

class monad_io_net_system (m : Type → Type → Type) [monad_io m] 
where
  socket : Type
  listen : string → ℕ → m io.error socket
  accept : socket → m io.error socket
  connect : string → m io.error socket
  recv : socket → ℕ → m io.error char_buffer
  send : socket → char_buffer → m io.error Unit
  close : socket → m io.error Unit

/- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode -/

class monad_io_file_system (m : Type → Type → Type) [monad_io m] 
where
  mk_file_handle : string → io.mode → Bool → m io.error (monad_io.handle m)
  is_eof : monad_io.handle m → m io.error Bool
  flush : monad_io.handle m → m io.error Unit
  close : monad_io.handle m → m io.error Unit
  read : monad_io.handle m → ℕ → m io.error char_buffer
  write : monad_io.handle m → char_buffer → m io.error Unit
  get_line : monad_io.handle m → m io.error char_buffer
  stdin : m io.error (monad_io.handle m)
  stdout : m io.error (monad_io.handle m)
  stderr : m io.error (monad_io.handle m)
  file_exists : string → m io.error Bool
  dir_exists : string → m io.error Bool
  remove : string → m io.error Unit
  rename : string → string → m io.error Unit
  mkdir : string → Bool → m io.error Bool
  rmdir : string → m io.error Bool

class monad_io_environment (m : Type → Type → Type) 
where
  get_env : string → m io.error (Option string)
  get_cwd : m io.error string
  set_cwd : string → m io.error Unit

-- we don't provide set_env as it is (thread-)unsafe (at least with glibc)

class monad_io_process (m : Type → Type → Type) [monad_io m] 
where
  child : Type
  stdin : child → monad_io.handle m
  stdout : child → monad_io.handle m
  stderr : child → monad_io.handle m
  spawn : io.process.spawn_args → m io.error child
  wait : child → m io.error ℕ
  sleep : ℕ → m io.error Unit

class monad_io_random (m : Type → Type → Type) 
where
  set_rand_gen : std_gen → m io.error Unit
  rand : ℕ → ℕ → m io.error ℕ

protected instance monad_io_is_monad (m : Type → Type → Type) (e : Type) [monad_io m] : Monad (m e) :=
  monad_io.monad e

protected instance monad_io_is_monad_fail (m : Type → Type → Type) [monad_io m] : monad_fail (m io.error) :=
  monad_fail.mk fun (α : Type) (s : string) => monad_io.fail io.error α (io.error.other s)

protected instance monad_io_is_alternative (m : Type → Type → Type) [monad_io m] : alternative (m io.error) :=
  alternative.mk
    fun (α : Type) =>
      monad_io.fail io.error α
        (io.error.other
          (string.str
            (string.str
              (string.str
                (string.str
                  (string.str
                    (string.str (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
                      (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
                    (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit1 1))))))))
                  (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
                (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
              (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
            (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))))))

