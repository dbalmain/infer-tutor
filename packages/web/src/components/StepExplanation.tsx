import { showType, type Type } from "@infer-tutor/lang";
import type { Step } from "@infer-tutor/algorithms";

function showSame(a: Type, b: Type): boolean {
  return showType(a) === showType(b);
}

export function StepExplanation({ step }: { step: Step }): JSX.Element | null {
  const body = explain(step);
  if (!body) return null;
  return <div className="explanation">{body}</div>;
}

function explain(step: Step): JSX.Element | null {
  switch (step.kind) {
    case "check-enter": {
      const isRoot = step.message.includes("root expression");
      return (
        <p>
          <strong>Check: entering node.</strong>{" "}
          Algorithm M passes an <em>expected type</em> down into each node
          (shown as <code>⇐ T</code> in the AST panel).
          Rather than synthesising a type and returning it,{" "}
          {isRoot
            ? "the root starts with a fresh unknown as the root expected type."
            : "this node must produce the expected type shown above — any mismatch is caught by immediate unification."}
        </p>
      );
    }

    case "infer-enter": {
      const isRoot = step.message.startsWith("infer root expression:");
      return (
        <p>
          <strong>Inference: entering node.</strong>{" "}
          Begin inferring {isRoot ? "the root expression" : "this subexpression"}.
          We descend into its parts, infer types for each, and combine them
          according to the rule for this expression's shape.
        </p>
      );
    }

    case "gen-enter": {
      const isRoot = step.message.includes("root expression");
      return (
        <p>
          <strong>Generation phase: entering node.</strong>{" "}
          {isRoot
            ? "Begin the constraint-generation walk from the root."
            : "Descend into this subexpression to assign type variables and collect constraints."}{" "}
          No unification happens here — we're only describing what equations
          the type must satisfy, deferring the solving to a later phase.
        </p>
      );
    }

    case "env-extend":
      return (
        <>
          <p>
            <strong>Extend environment.</strong> Before inferring the
            child, we add a new binding to the environment so the child
            can look it up.
          </p>
          <p>
            For lambda bodies, the parameter is added with its fresh type
            variable as a monomorphic scheme (no <code>forall</code>) — that's
            why lambda parameters are not polymorphic. For let bodies, the
            bound name is added with the generalised scheme just computed,
            making it polymorphic at every use site.
          </p>
        </>
      );

    case "check-exit":
      return (
        <>
          <p>
            <strong>Check: leaving node.</strong>{" "}
            The substitution shown here has grown since <code>check-enter</code>:
            it contains any variable bindings discovered inside this check (e.g.{" "}
            <code>t3 ↦ t2</code> from unifying an instantiated type with the
            expected type).
          </p>
          <p>
            The parent will now apply this substitution to its own pending
            types — for example, resolving the lambda's expected type{" "}
            <code>t1</code> to <code>t2 → t2</code>. Those applications
            appear as the next few <code>subst-apply</code> steps before
            the parent's own <code>check-exit</code>.
          </p>
        </>
      );

    case "infer-exit":
      return (
        <p>
          <strong>Inference: leaving node.</strong>{" "}
          This subexpression's type is now known. It returns up to the
          surrounding context where it'll be unified, applied, or just
          returned as the program's overall type.
        </p>
      );

    case "gen-exit":
      return (
        <p>
          <strong>Generation phase: leaving node.</strong> All constraints
          for this subexpression have been emitted. The type shown may still
          be a fresh variable — it will be resolved once the solve phase works
          through the constraint list.
        </p>
      );

    case "fresh-param": {
      const isAlgoM = step.message.includes("decomposing expected type");
      if (isAlgoM) {
        return (
          <>
            <p>
              Algorithm M knows the <em>expected type</em> of this lambda
              (from the parent). To discover the parameter and body types,
              it introduces two fresh variables and immediately unifies the
              expected type with <code>α → β</code>.
            </p>
            <p>
              This is the top-down counterpart of W's fresh-param: instead of
              inventing a placeholder and waiting for the body to constrain it,
              M demands the expected function type up front.
            </p>
          </>
        );
      }
      return (
        <>
          <p>
            Lambda parameters have no annotation, so we don't yet know their
            types. We give the parameter a <em>fresh type variable</em>{" "}
            (one not used anywhere else) as a placeholder.
          </p>
          <p>
            As we infer the body, every way the parameter is used will
            constrain this variable through unification. If nothing pins it
            down, it stays polymorphic.
          </p>
        </>
      );
    }

    case "fresh-app": {
      const isAlgoM = step.message.startsWith("fresh") && step.message.includes("argument;");
      if (isAlgoM) {
        return (
          <>
            <p>
              Algorithm M already knows the <em>result</em> type (it's the
              expected type passed in from the parent). What it doesn't know
              yet is the <em>argument</em> type, so it invents a fresh
              variable for that.
            </p>
            <p>
              The function is then checked against{" "}
              <code>freshArg → expectedResult</code>, and the argument
              against <code>σ(freshArg)</code> after the function check
              has possibly bound <code>freshArg</code>.
            </p>
          </>
        );
      }
      return (
        <>
          <p>
            The result type of a function application is unknown ahead of
            time, so we invent a fresh type variable for it.
          </p>
          <p>
            Next we'll unify the function's type with{" "}
            <code>argType -&gt; freshVar</code>. That single unification
            does two things: it confirms the function accepts this argument
            type, and it pins down what <code>freshVar</code> must be —
            i.e., the result type.
          </p>
        </>
      );
    }

    case "lookup": {
      const name =
        step.detail && "name" in step.detail ? step.detail.name : undefined;
      const sc = name ? step.env.get(name) : undefined;
      return (
        <>
          <p>
            <strong>Environment lookup.</strong> The Var rule of{" "}
            <code>infer</code> says: to type-check a variable, find its
            scheme in the environment. We look up <code>{name}</code> and
            get back{" "}
            {sc && sc.vars.length > 0 ? (
              <>
                a polymorphic scheme (it starts with{" "}
                <code>forall {sc.vars.join(" ")}.</code>).
              </>
            ) : (
              <>a monomorphic scheme (no <code>forall</code>).</>
            )}
          </p>
          <p>
            If the name isn't in the environment, the program is
            ill-formed — that's an unbound-variable error, not a
            type-inference failure. Next, we'll instantiate the scheme.
          </p>
        </>
      );
    }

    case "instantiate": {
      const name =
        step.detail && "name" in step.detail ? step.detail.name : undefined;
      const sc = name ? step.env.get(name) : undefined;
      if (sc && sc.vars.length > 0) {
        return (
          <>
            <p>
              <strong>Instantiation.</strong> The scheme we just looked up
              is polymorphic — it begins with{" "}
              <code>forall {sc.vars.join(" ")}.</code> Each use of{" "}
              <code>{name}</code> needs its own copy, so we replace each
              bound variable with a fresh type variable.
            </p>
            <p>
              This is the mechanism behind let-polymorphism: two uses of{" "}
              <code>{name}</code> in the same expression get independent
              fresh variables, so they can specialise to different types
              without conflict.
            </p>
          </>
        );
      }
      return (
        <p>
          <strong>Instantiation.</strong> The scheme for <code>{name}</code>{" "}
          has no bound variables (it's monomorphic), so instantiation
          returns the type as-is. The step is conceptually the same as for
          polymorphic schemes; there just happens to be nothing to rename.
        </p>
      );
    }

    case "generalize":
      return (
        <>
          <p>
            <strong>Generalisation.</strong> At a <code>let</code> binding,
            we close over type variables that are free in the inferred type
            but NOT free in the surrounding environment. These become bound
            by <code>forall</code>.
          </p>
          <p>
            This is the difference between <code>let</code> and{" "}
            <code>\</code>: <code>let</code> generalises before adding the
            name to the environment, so the body can use the name at
            multiple types. A lambda parameter never gets generalised — it
            stays monomorphic within its body.
          </p>
        </>
      );

    case "unify-enter":
      return (
        <>
          <p>
            <strong>Unification.</strong> We need these two types to be
            equal under some substitution. The algorithm walks both in
            parallel:
          </p>
          <ul>
            <li>
              Same constructor on both sides (e.g. both{" "}
              <code>{"->"}</code>): unify the children pairwise.
            </li>
            <li>
              One side is a type variable: bind it to the other side
              (subject to the occurs check).
            </li>
            <li>Different constructors: type error.</li>
          </ul>
        </>
      );

    case "unify-success":
      return (
        <p>
          The two sides were unified. Any new variable bindings discovered
          during the walk have been composed into the running substitution
          on the right.
        </p>
      );

    case "unify-fail":
      return (
        <p>
          The two sides cannot be made equal under any substitution.
          Either the head constructors disagree, or binding would require a
          type to contain itself (the occurs check — typical of trying to
          give <code>\x -&gt; x x</code> a type).
        </p>
      );

    case "unify-recurse":
      return (
        <p>
          <strong>Recurse into unify.</strong> Both sides are function
          types, so unification descends into the corresponding children.
          The substitution learned from unifying the earlier child is
          carried forward into the next call — that's how a binding made
          on one side gets enforced on the other.
        </p>
      );

    case "bind-var":
      return (
        <>
          <p>
            <strong>Bind variable.</strong> One side is a type variable;
            we extend the substitution with{" "}
            {step.detail && "name" in step.detail ? (
              <>
                <code>{step.detail.name} ↦ {/* shown in message */}</code>
              </>
            ) : null}{" "}
            this binding so that subsequent uses see the variable as the
            other type.
          </p>
          <p>
            Before binding, we run the <em>occurs check</em>: if the
            variable appears inside the type we'd bind it to, we'd be
            asking for an infinite type — so we refuse and raise a type
            error. (That's the failure mode of <code>\x -&gt; x x</code>.)
          </p>
          <p>
            σ on the right shows the new binding inserted alongside the
            existing entries. If any of those existing RHS still mention
            the just-bound variable, the next step
            (<code>subst-compose</code>) rewrites them to keep σ
            idempotent.
          </p>
        </>
      );

    case "subst-compose":
      return (
        <>
          <p>
            <strong>Compose into σ.</strong> Adding a new binding to the
            substitution isn't just an insert. The new mapping must also
            be applied to the right-hand side of every existing entry —
            otherwise σ wouldn't be idempotent (applying it once vs.
            twice could give different answers).
          </p>
          <p>
            In the previous step, σ contained the new binding next to
            unchanged old entries. Now those old entries' RHS have been
            rewritten through the new binding.
          </p>
        </>
      );

    case "subst-apply": {
      const isNoop =
        step.detail &&
        "input" in step.detail &&
        showSame(step.detail.input, step.detail.output);
      if (isNoop) {
        return (
          <p>
            <strong>Apply substitution.</strong> The algorithm consults the
            current substitution here. Nothing in this type contains a
            variable that the substitution maps, so the result is identical
            to the input.
          </p>
        );
      }
      return (
        <>
          <p>
            <strong>Apply substitution.</strong> The algorithm has reached
            a point where it needs the most up-to-date version of a type.
            We walk the type and replace each TVar with whatever the
            substitution says it equals (recursively, until fixed).
          </p>
          <p>
            This is how earlier unifications "flow forward": once a
            variable was bound, every subsequent place that consults the
            substitution sees the bound value.
          </p>
        </>
      );
    }

    case "done":
      return (
        <p>
          The algorithm has finished. Applying the final substitution to the
          root type gives the program's type.
        </p>
      );

    case "emit-constraint":
      return (
        <>
          <p>
            <strong>Constraint emitted.</strong> W′ doesn't unify immediately
            — instead it records an equation between two types and defers the
            work to the solve phase. This separates <em>typing structure</em>{" "}
            (what equations the grammar requires) from{" "}
            <em>solving</em> (finding the substitution that satisfies them).
          </p>
          <p>
            The constraint list on the right accumulates all such equations.
            You'll see them solved one by one after generation completes.
          </p>
        </>
      );

    case "solve-phase": {
      const pending = step.constraints.filter(
        (c) => !step.solvedConstraintIds.includes(c.id),
      ).length;
      if (pending === 0) {
        return (
          <>
            <p>
              <strong>No constraints to solve here.</strong> The value
              expression generated no deferred equations, so there's nothing
              to unify before generalizing. We proceed straight to{" "}
              <code>generalize</code>.
            </p>
            <p>
              This is common for lambdas and variables, which never emit
              constraints — only applications and conditionals do.
            </p>
          </>
        );
      }
      return (
        <>
          <p>
            <strong>Entering solve phase.</strong> All constraints for this
            scope have been generated. Now unification works through the list,
            building up the substitution as it goes.
          </p>
          <p>
            For let-bindings this happens <em>before</em> generalizing — you
            need the solved type to know which variables are safe to close
            over with <code>forall</code>.
          </p>
        </>
      );
    }

    case "solve-constraint":
      return (
        <p>
          <strong>Solving a constraint.</strong> Apply the current
          substitution to both sides, then unify them. Any new variable
          bindings discovered here are composed into the running substitution
          and immediately reflected in the AST view.
        </p>
      );
  }
}
