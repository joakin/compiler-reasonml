module Result = {
  type t('good, 'bad) =
    | Ok('good)
    | Err('bad);

  let map = (result: t('a, 'err), fn: 'a => 'c): t('c, 'err) =>
    switch (result) {
    | Ok(x) => Ok(fn(x))
    | Err(x) => Err(x)
    };

  let map2 =
      (r1: t('a, 'err), r2: t('b, 'err), fn: ('a, 'b) => 'c): t('c, 'err) =>
    switch (r1, r2) {
    | (Ok(x), Ok(y)) => Ok(fn(x, y))
    | (Err(x), _)
    | (_, Err(x)) => Err(x)
    };

  let andThen = (r1: t('a, 'err), fn: 'a => t('b, 'err)): t('b, 'err) =>
    switch (r1) {
    | Ok(x) => fn(x)
    | Err(x) => Err(x)
    };
};

module Ast = {
  type expression =
    | Float(float)
    | String(string)
    | Var(string)
    | Fn(fn)
    | Call(call)
    | If(if_)
  and fn = {
    param: string,
    body: expression,
  }
  and call = {
    fn: expression,
    arg: expression,
  }
  and if_ = {
    cond: expression,
    trueBranch: expression,
    falseBranch: expression,
  };

  let example: expression =
    Fn({
      param: "x",
      body:
        If({
          cond: Var("x"),
          trueBranch: Float(1.),
          falseBranch: Call({fn: Var("f"), arg: Var("x")}),
        }),
    });
};

module Type = {
  type t =
    | Named(string)
    | Var(string)
    | Fun(fun_)
  and fun_ = {
    from: t,
    to_: t,
  };

  let rec contains = (t: t, name: string): bool =>
    switch (t) {
    | Named(_) => false
    | Var(n) => n === name
    | Fun({from, to_}) => contains(from, name) || contains(to_, name)
    };

  let rec toString = (t: t): string =>
    switch (t) {
    | Named(n) => n
    | Var(n) => n
    | Fun({from, to_}) =>
      "(" ++ toString(from) ++ " -> " ++ toString(to_) ++ ")"
    };
};

module TypeCheck = {
  module Map = Belt.Map.String;

  type error =
    | CircularReference(string)
    | TypeMismatch(string)
    | UnboundVariable(string)
    | UnexpectedError(string)
    | NotImplemented;

  module Context = {
    type t = {
      /* Mutable and global to all context for ease of use */
      mutable nextTVar: float,
      env: Map.t(Type.t),
    };

    let get = Map.get;

    let newTVar = (ctx: t): Type.t => {
      let tvar = Type.Var("T" ++ string_of_float(ctx.nextTVar));
      ctx.nextTVar = ctx.nextTVar +. 1.;
      tvar;
    };

    let newBinding = (ctx: t, name: string, tvar: Type.t): t => {
      ...ctx,
      env: Map.set(ctx.env, name, tvar),
    };

    let mapEnv = ({env} as ctx: t, fn: Type.t => Type.t): t => {
      ...ctx,
      env: Map.map(env, type_ => fn(type_)),
    };
  };

  module Substitution = {
    type t = Map.t(Type.t);

    let empty = Map.empty;
    let get = Map.get;

    let toString = (m: t): string =>
      "{"
      ++ (
        Map.toArray(m)
        |> Array.map(((key, value)) =>
             key ++ ": " ++ Type.toString(value) ++ ","
           )
        |> Array.fold_left((r, s) => r ++ " " ++ s, "")
      )
      ++ "}";

    /*
     Replace the type variables in a type that are present in the given
     substitution and return the type with those variables substituted
     eg. Applying the substitution {"a": Bool, "b": Int} to a type (a -> b)
     will give type (Bool -> Int)
     */
    let rec applySubstitutionToType = (subst: t, type_: Type.t): Type.t =>
      switch (type_) {
      | Named(_) => type_
      | Var(name) =>
        switch (get(subst, name)) {
        | Some(foundType) => foundType
        | None => type_
        }
      | Fun({from, to_}) =>
        Fun({
          from: applySubstitutionToType(subst, from),
          to_: applySubstitutionToType(subst, to_),
        })
      };

    let applySubstitutionToCtx = (subst: t, ctx: Context.t): Context.t =>
      Context.mapEnv(ctx, applySubstitutionToType(subst));

    let varBind = (name: string, t: Type.t): Result.t(t, error) =>
      switch (t) {
      | Var(n) when n == name => Result.Ok(empty)
      | Var(_) => Result.Ok(Map.set(empty, name, t))
      | _ when Type.contains(t, name) =>
        Result.Err(CircularReference(Type.toString(t)))
      | _ => Result.Ok(Map.set(empty, name, t))
      };

    let compose = (s1: t, s2: t): t =>
      Map.map(s2, type_ => applySubstitutionToType(s1, type_))
      |> Map.merge(s1, _, (_key, _t1, t2) => t2);

    let rec unify = (t1: Type.t, t2: Type.t): Result.t(t, error) =>
      switch (t1, t2) {
      | (Type.Named(n1), Type.Named(n2)) when n1 === n2 => Result.Ok(empty)
      | (Type.Var(v1), _) => varBind(v1, t2)
      | (_, Type.Var(v2)) => varBind(v2, t1)
      | (Type.Fun(f1), Type.Fun(f2)) =>
        switch (unify(f1.from, f2.from)) {
        | Result.Ok(s1) =>
          switch (
            unify(
              applySubstitutionToType(s1, f1.to_),
              applySubstitutionToType(s1, f2.to_),
            )
          ) {
          | Result.Ok(s2) => Result.Ok(compose(s1, s2))
          | err => err
          }
        | err => err
        }
      | _ =>
        Result.Err(
          TypeMismatch(
            "Type mismatch:\n    Expected "
            ++ Type.toString(t1)
            ++ "}\n    Found "
            ++ Type.toString(t2),
          ),
        )
      };
  };

  let rec infer =
          ({env} as ctx: Context.t, e: Ast.expression)
          : Result.t((Type.t, Substitution.t), error) =>
    switch (e) {
    | Ast.Float(_) => Result.Ok((Type.Named("Float"), Substitution.empty))
    | Ast.String(_) => Result.Ok((Type.Named("String"), Substitution.empty))
    | Ast.Var(name) =>
      switch (Context.get(env, name)) {
      | Some(type_) => Result.Ok((type_, Substitution.empty))
      | None => Result.Err(UnboundVariable(name))
      }
    | Ast.Fn({param, body}) =>
      let newTVar = Context.newTVar(ctx);
      let newCtx = Context.newBinding(ctx, param, newTVar);

      infer(newCtx, body)
      |> Result.map(_, ((bodyType, subst)) =>
           (
             Type.Fun({
               from: Substitution.applySubstitutionToType(subst, newTVar),
               to_: bodyType,
             }),
             subst,
           )
         );
    | Ast.Call({fn, arg}) =>
      switch (infer(ctx, fn)) {
      | Result.Ok((fnType, s1)) =>
        switch (infer(Substitution.applySubstitutionToCtx(s1, ctx), arg)) {
        | Result.Ok((argType, s2)) =>
          let s3 = Substitution.compose(s1, s2);
          let tvar = Context.newTVar(ctx);
          let s4 =
            Substitution.unify(Type.Fun({from: argType, to_: tvar}), fnType);
          let fnType' =
            Result.map(s4, s4 =>
              Substitution.applySubstitutionToType(s4, fnType)
            );
          Result.map2(s4, fnType', (s4, fnType') => (s4, fnType'))
          |> Result.andThen(_, ((s4, fnType')) =>
               switch (fnType') {
               | Type.Fun({from, to_}) =>
                 let s5 = Substitution.compose(s3, s4);
                 let s6 =
                   Substitution.applySubstitutionToType(s5, from)
                   |> Substitution.unify(_, argType);
                 let s7 = Result.map(s6, s6 => Substitution.compose(s5, s6));
                 Result.map(s7, s7 =>
                   (Substitution.applySubstitutionToType(s7, to_), s7)
                 );
               | _ =>
                 Result.Err(
                   UnexpectedError(
                     Type.toString(fnType)
                     ++ " substitution didn't return a Type.Fun. Returned "
                     ++ Type.toString(fnType'),
                   ),
                 )
               }
             );
        | err => err
        }
      | err => err
      }
    | Ast.If(_) => Result.Err(NotImplemented)
    };
};

let test = (ctx, ast): unit => {
  let res = TypeCheck.infer(ctx, ast);

  switch (res) {
  | Result.Ok((t, subst)) =>
    Js.log3(
      "Success",
      Type.toString(t),
      "\n" ++ TypeCheck.Substitution.toString(subst),
    )
  | Result.Err(err) =>
    TypeCheck.(
      switch (err) {
      | CircularReference(s) => Js.log2("Circular reference: ", s)
      | TypeMismatch(s) => Js.log2("Type mismatch: ", s)
      | UnboundVariable(s) => Js.log2("Unbound variable:", s)
      | UnexpectedError(s) => Js.log2("Unexpected error:", s)
      | NotImplemented => Js.log("Feature not implemented")
      }
    )
  };
};

let ctx = (): TypeCheck.Context.t => {
  nextTVar: 0.,
  env:
    Belt.Map.String.fromArray([|
      (
        "+",
        Type.(
          Fun({
            from: Named("Float"),
            to_: Fun({from: Named("Float"), to_: Named("Float")}),
          })
        ),
      ),
      (
        "++",
        Type.(
          Fun({
            from: Named("String"),
            to_: Fun({from: Named("String"), to_: Named("String")}),
          })
        ),
      ),
      (
        "String.length",
        Type.(Fun({from: Named("String"), to_: Named("Float")})),
      ),
    |]),
};

test(
  ctx(),
  Ast.(Fn({param: "x", body: Call({fn: Var("f"), arg: Var("x")})})),
);

test(
  ctx(),
  Ast.(Fn({param: "x", body: Call({fn: Var("+"), arg: Var("x")})})),
);

test(
  ctx(),
  Ast.(
    Fn({
      param: "x",
      body: Fn({param: "y", body: Call({fn: Var("+"), arg: Var("x")})}),
    })
  ),
);

test(
  ctx(),
  Ast.(
    Fn({param: "s", body: Call({fn: Var("String.length"), arg: Var("s")})})
  ),
);

/* This should return Float -> Float but it returns T0 -> Float. BUG */
test(
  ctx(),
  Ast.(
    Fn({
      param: "x",
      body:
        Call({fn: Call({fn: Var("+"), arg: Var("x")}), arg: Float(5.)}),
    })
  ),
);
