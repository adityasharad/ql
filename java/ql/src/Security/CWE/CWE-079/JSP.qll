import java
import semmle.code.java.frameworks.Servlets
import semmle.code.java.dataflow.TaintTracking2
import semmle.code.java.dataflow.FlowSources

/**
 * The interface `javax.servlet.RequestDispatcher`.
 */
class RequestDispatcher extends RefType {
  RequestDispatcher() { hasQualifiedName("javax.servlet", "RequestDispatcher") }
}

/**
 * The method `getRequestDispatcher(string)` declared in `javax.servlet.ServletRequest`.
 */
class ServletRequestGetRequestDispatcherMethod extends Method {
  ServletRequestGetRequestDispatcherMethod() {
    getDeclaringType() instanceof ServletRequest and
    hasName("getRequestDispatcher") and
    getNumberOfParameters() = 1
  }
}

/**
 * The method `forward` declared in `javax.servlet.RequestDispatcher`.
 */
class RequestDispatcherForwardMethod extends Method {
  RequestDispatcherForwardMethod() {
    getDeclaringType() instanceof RequestDispatcher and
    hasName("forward") and
    getNumberOfParameters() = 2
  }
}

/**
 * The method `include` declared in `javax.servlet.RequestDispatcher`.
 */
class RequestDispatcherIncludeMethod extends Method {
  RequestDispatcherIncludeMethod() {
    getDeclaringType() instanceof RequestDispatcher and
    hasName("include") and
    getNumberOfParameters() = 2
  }
}

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
  JspParamFlowSource() {
    this.asExpr().(StringLiteral).getValue().matches("${param.%}%")
  }

  override string getSourceType() {
    result = "JSP parameter"
  }
}

class JspTaintStep extends TaintTracking2::AdditionalTaintStep {
  override predicate step(DataFlow::Node source, DataFlow::Node target) {
      // x -> proprietaryEvaluate(x, ...)
      exists(MethodAccess call |
        call.getArgument(0) = source.asExpr() and
        call = target.asExpr() and
        call.getMethod() instanceof ProprietaryEvaluateMethod
      )
  }
}