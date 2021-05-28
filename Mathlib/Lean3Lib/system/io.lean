/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.Lean3Lib.system.io_interface
import PostPort

universes u_1 

namespace Mathlib

/- The following constants have a builtin implementation -/

axiom io_core : Type → Type → Type/- Auxiliary definition used in the builtin implementation of monad_io_random_impl -/

def io_rand_nat : std_gen → ℕ → ℕ → ℕ × std_gen :=
  rand_nat

instance monad_io_impl : monad_io io_coreinstance monad_io_terminal_impl : monad_io_terminal io_coreinstance monad_io_net_system_impl : monad_io_net_system io_coreinstance monad_io_file_system_impl : monad_io_file_system io_coreinstance monad_io_environment_impl : monad_io_environment io_coreinstance monad_io_process_impl : monad_io_process io_coreinstance monad_io_random_impl : monad_io_random io_coreprotected instance io_core_is_monad (e : Type) : Monad (io_core e) :=
  Mathlib.monad_io_is_monad io_core e

protected instance io_core_is_monad_fail : monad_fail (io_core io.error) :=
  Mathlib.monad_io_is_monad_fail io_core

protected instance io_core_is_alternative : alternative (io_core io.error) :=
  Mathlib.monad_io_is_alternative io_core

def io (α : Type)  :=
  io_core sorry α

namespace io


/- Remark: the following definitions can be generalized and defined for any (m : Type -> Type -> Type)
   that implements the required type classes. However, the generalized versions are very inconvenient to use,
   (example: `#eval io.put_str "hello world"` does not work because we don't have enough information to infer `m`.).
-/

def iterate {e : Type} {α : Type} (a : α) (f : α → io_core e (Option α)) : io_core e α :=
  monad_io.iterate e α a f

def forever {e : Type} (a : io_core e Unit) : io_core e Unit :=
  iterate Unit.unit fun (_x : Unit) => a >> return (some Unit.unit)

-- TODO(Leo): delete after we merge #1881

def catch {e₁ : Type} {e₂ : Type} {α : Type} (a : io_core e₁ α) (b : e₁ → io_core e₂ α) : io_core e₂ α :=
  monad_io.catch e₁ e₂ α a b

def finally {α : Type} {e : Type} (a : io_core e α) (cleanup : io_core e Unit) : io_core e α :=
  do 
    let res ← catch (sum.inr <$> a) (return ∘ sum.inl)
    cleanup 
    sorry

protected def fail {α : Type} (s : string) : io α :=
  monad_io.fail error α (error.other s)

def put_str : string → io Unit :=
  monad_io_terminal.put_str

def put_str_ln (s : string) : io Unit :=
  put_str s >> put_str (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 1)))))

def get_line : io string :=
  monad_io_terminal.get_line

def cmdline_args : io (List string) :=
  return (monad_io_terminal.cmdline_args io_core)

def print {α : Type u_1} [has_to_string α] (s : α) : io Unit :=
  function.comp put_str to_string s

def print_ln {α : Type u_1} [has_to_string α] (s : α) : io Unit :=
  print s >> put_str (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 1)))))

def handle  :=
  monad_io.handle io_core

def mk_file_handle (s : string) (m : mode) (bin : optParam Bool false) : io handle :=
  monad_io_file_system.mk_file_handle s m bin

def stdin : io handle :=
  monad_io_file_system.stdin

def stderr : io handle :=
  monad_io_file_system.stderr

def stdout : io handle :=
  monad_io_file_system.stdout

namespace env


def get (env_var : string) : io (Option string) :=
  monad_io_environment.get_env env_var

/-- get the current working directory -/
def get_cwd : io string :=
  monad_io_environment.get_cwd

/-- set the current working directory -/
def set_cwd (cwd : string) : io Unit :=
  monad_io_environment.set_cwd cwd

end env


namespace net


def socket  :=
  monad_io_net_system.socket io_core

def listen : string → ℕ → io socket :=
  monad_io_net_system.listen

def accept : socket → io socket :=
  monad_io_net_system.accept

def connect : string → io socket :=
  monad_io_net_system.connect

def recv : socket → ℕ → io char_buffer :=
  monad_io_net_system.recv

def send : socket → char_buffer → io Unit :=
  monad_io_net_system.send

def close : socket → io Unit :=
  monad_io_net_system.close

end net


namespace fs


def is_eof : handle → io Bool :=
  monad_io_file_system.is_eof

def flush : handle → io Unit :=
  monad_io_file_system.flush

def close : handle → io Unit :=
  monad_io_file_system.close

def read : handle → ℕ → io char_buffer :=
  monad_io_file_system.read

def write : handle → char_buffer → io Unit :=
  monad_io_file_system.write

def get_char (h : handle) : io char := sorry

def get_line : handle → io char_buffer :=
  monad_io_file_system.get_line

def put_char (h : handle) (c : char) : io Unit :=
  write h (buffer.push_back mk_buffer c)

def put_str (h : handle) (s : string) : io Unit :=
  write h (buffer.append_string mk_buffer s)

def put_str_ln (h : handle) (s : string) : io Unit :=
  put_str h s >> put_str h (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 1)))))

def read_to_end (h : handle) : io char_buffer :=
  iterate mk_buffer
    fun (r : char_buffer) =>
      do 
        let done ← is_eof h 
        ite (↥done) (return none)
            (do 
              let c ← read h (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 (bit0 1))))))))))
              return (some (r ++ c)))

def read_file (s : string) (bin : optParam Bool false) : io char_buffer :=
  do 
    let h ← mk_file_handle s mode.read bin 
    read_to_end h

def file_exists : string → io Bool :=
  monad_io_file_system.file_exists

def dir_exists : string → io Bool :=
  monad_io_file_system.dir_exists

def remove : string → io Unit :=
  monad_io_file_system.remove

def rename : string → string → io Unit :=
  monad_io_file_system.rename

def mkdir (path : string) (recursive : optParam Bool false) : io Bool :=
  monad_io_file_system.mkdir path recursive

def rmdir : string → io Bool :=
  monad_io_file_system.rmdir

end fs


namespace proc


def child  :=
  monad_io_process.child io_core

def child.stdin : child → handle :=
  monad_io_process.stdin

def child.stdout : child → handle :=
  monad_io_process.stdout

def child.stderr : child → handle :=
  monad_io_process.stderr

def spawn (p : process.spawn_args) : io child :=
  monad_io_process.spawn p

def wait (c : child) : io ℕ :=
  monad_io_process.wait c

def sleep (n : ℕ) : io Unit :=
  monad_io_process.sleep n

end proc


def set_rand_gen : std_gen → io Unit :=
  monad_io_random.set_rand_gen

def rand (lo : optParam ℕ (prod.fst std_range)) (hi : optParam ℕ (prod.snd std_range)) : io ℕ :=
  monad_io_random.rand lo hi

end io


/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def io.cmd (args : io.process.spawn_args) : io string := sorry

