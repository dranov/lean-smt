import Lean
import Smt.Translate.Term
open Lean

initialize
  registerTraceClass `smt.cache

register_option smt.globalCache : Bool := {
  defValue := false
  descr := "Whether to cache the SMT translation of expressions across calls to `smt`."
}

structure GlobalCache where
    cache : Std.HashMap Expr (Option (Smt.Term × NameSet × FVarIdSet)) := {}
deriving Inhabited

def GlobalCache.merge (a b : GlobalCache) : GlobalCache := Id.run do
  let mut cache := a.cache
  for (k, v) in b.cache do
      cache := cache.alter k (fun ex =>
        match (ex, v) with
        | (.none, _) | (.some .none, _) => v
        | (_, .none) => ex
        | (.some $ .some (tm, depConsts, depFVars), .some (_tm', depConsts', depFVars')) =>
           .some $ .some (tm, depConsts.union depConsts', depFVars.union depFVars')
      )
  { cache := cache }

@[inline] def GlobalCache.overwrite (_a b : GlobalCache) := b

initialize globalCache : SimplePersistentEnvExtension GlobalCache GlobalCache ←
  registerSimplePersistentEnvExtension {
    name := `globalCache
    -- addEntryFn := fun env add => env.overwrite add
    addEntryFn := fun _ _ => default
    addImportedFn := fun _ => default
    asyncMode := .local
    exported := false
  }

def GlobalCache.reset [Monad m] [MonadEnv m] : m Unit := do
  Lean.setEnv $ globalCache.setState (<- getEnv) default
