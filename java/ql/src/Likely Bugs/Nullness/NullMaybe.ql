/**
 * @name Dereferenced variable may be null
 * @description Dereferencing a variable whose value may be 'null' may cause a
 *              'NullPointerException'.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id java/dereferenced-value-may-be-null
 * @tags reliability
 *       correctness
 *       exceptions
 *       external/cwe/cwe-476
 *       non-local
 */

import java
private import semmle.code.java.dataflow.SSA
private import semmle.code.java.dataflow.Nullness

/** A `@NotNull` annotation using the type `javax.validation.constraints.NotNull`. */
class NotNullAnnotation extends Annotation {
  NotNullAnnotation() {
    this.getType().hasQualifiedName("javax.validation.constraints", "NotNull")
  }
}

/**
 * A call to a method annotated with `@NotNull`.
 * Such a call is guaranteed to return a non-`null` value, assuming the `@NotNull` annotation is respected.
 */
class NonNullMethodAccess extends MethodAccess {
  NonNullMethodAccess() {
    this.getMethod().getAnAnnotation() instanceof NotNullAnnotation
  }
}

/** Gets an expression that is explicitly assigned to the given variable, if any. */
Expr getAnExplicitSource(SsaSourceVariable sourceVar) {
  result = sourceVar.getAnSsaVariable().(SsaExplicitUpdate).getDefiningExpr().(VariableAssign).getSource()
}

from VarAccess access, SsaSourceVariable var, string msg, Expr reason
where
  nullDeref(var, access, msg, reason) and
  // Exclude definite nulls here, as these are covered by `NullAlways.ql`.
  not alwaysNullDeref(var, access) and
  // Exclude values returned by methods annotated with `@NotNull`.
  not getAnExplicitSource(var) instanceof NonNullMethodAccess
select access, "Variable $@ may be null here " + msg + ".", var.getVariable(),
  var.getVariable().getName(), reason, "this"
