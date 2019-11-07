/**
 * @name Cross-site scripting
 * @description Writing user input directly to a web page
 *              allows for a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id java/xss
 * @tags security
 *       external/cwe/cwe-079
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.dataflow.TaintTracking2
import semmle.code.java.security.XSS
import DataFlow2::PathGraph

/**
 * The method `proprietaryEvaluate` declared in `org.apache.jasper.runtime.PageContextImpl`.
 * This is used to evaluate JSP Expression Language (EL) expressions
 * present on a page.
 * See https://tomcat.apache.org/tomcat-7.0-doc/api/org/apache/jasper/runtime/PageContextImpl.html#proprietaryEvaluate.
 */
class ProprietaryEvaluateMethod extends Method {
  ProprietaryEvaluateMethod() {
    getDeclaringType().hasQualifiedName("org.apache.jasper.runtime", "PageContextImpl") and
    hasName("proprietaryEvaluate")
  }
}

class JspParamFlowSource extends RemoteFlowSource {
  JspParamFlowSource() { this.asExpr().(StringLiteral).getValue().matches("${param.%}%") }

  override string getSourceType() { result = "JSP parameter" }
}

// class JspTaintStep extends TaintTracking2::AdditionalTaintStep {
//   override predicate step(DataFlow::Node source, DataFlow::Node target) {
//     // x -> proprietaryEvaluate(x, ...)
//     exists(MethodAccess call |
//       call.getArgument(0) = source.asExpr() and
//       call = target.asExpr() and
//       call.getMethod() instanceof ProprietaryEvaluateMethod
//     )
//   }
// }
class XSSConfig extends TaintTracking2::Configuration {
  XSSConfig() { this = "XSSConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof XssSink and sink instanceof DataFlow::ExprNode }

  override predicate isSanitizer(DataFlow::Node node) {
    node.getType() instanceof NumericType or node.getType() instanceof BooleanType
  }

  override predicate isAdditionalTaintStep(DataFlow::Node source, DataFlow::Node target) {
    exists(MethodAccess call |
      call.getArgument(0) = source.asExpr() and
      call = target.asExpr() and
      call.getMethod() instanceof ProprietaryEvaluateMethod
    )
  }
}

from DataFlow2::PathNode source, DataFlow2::PathNode sink, XSSConfig conf
where conf.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Cross-site scripting vulnerability due to $@.",
  source.getNode(), "user-provided value"
