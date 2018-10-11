/**
 * @name Test
 * @description Test
 * @kind problem
 * @problem.severity error
 * @id csharp/test
 */
 
import csharp

predicate isNotApproved(MemberAccess ma) {
    ma.getTarget().getDeclaringType().hasQualifiedName("X", "Y") 
    and (ma.getTarget().getName().matches("%A%")
      or ma.getTarget().getName().matches("%B")
      or ma.getTarget().getName().matches("C%"))
}

from MemberAccess ma
where ma.fromSource()
  and isNotApproved(ma) 
select strictcount(ma), "Use of " + ma.getTarget().getName() + "." 