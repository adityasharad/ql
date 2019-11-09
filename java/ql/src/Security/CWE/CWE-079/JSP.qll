import java
import semmle.code.java.frameworks.Servlets
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.security.XSS

/**
 * The interface `javax.servlet.RequestDispatcher`.
 */
class RequestDispatcher extends RefType {
  RequestDispatcher() { hasQualifiedName("javax.servlet", "RequestDispatcher") }
}

/**
 * The interface `javax.servlet.ServletContext`.
 */
class ServletContext extends RefType {
  ServletContext() { hasQualifiedName("javax.servlet", "ServletContext") }
}

/**
 * A method `getRequestDispatcher(string)` declared in
 * `javax.servlet.ServletRequest` or `javax.servlet.ServletContext`.
 */
class GetRequestDispatcherMethod extends Method {
  GetRequestDispatcherMethod() {
    (
      getDeclaringType() instanceof ServletRequest or
      getDeclaringType() instanceof ServletContext
    ) and
    hasName("getRequestDispatcher") and
    getNumberOfParameters() = 1
  }
}

/**
 * The method `getAttribute` declared in `javax.servlet.ServletRequest`.
 */
class ServletRequestGetAttributeMethod extends Method {
  ServletRequestGetAttributeMethod() {
    getDeclaringType() instanceof ServletRequest and
    hasName("getAttribute")
  }
}

/**
 * The method `setAttribute` declared in `javax.servlet.ServletRequest`.
 */
class ServletRequestSetAttributeMethod extends Method {
  ServletRequestSetAttributeMethod() {
    getDeclaringType() instanceof ServletRequest and
    hasName("setAttribute")
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

/** A reference to a JSP include parameter, as a source of remote user input. */
class JspParamFlowSource extends RemoteFlowSource {
  JspParamFlowSource() { this.asExpr().(StringLiteral).getValue().matches("${param.%}%") }

  override string getSourceType() { result = "JSP parameter" }
}

/** Taint tracking step from `x` to `org.apache.jasper.runtime.PageContextImpl.proprietaryEvaluate(x)`. */
private class JspProprietaryEvaluateTaintStep extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node source, DataFlow::Node target) {
    exists(MethodAccess call |
      call.getArgument(0) = source.asExpr() and
      call = target.asExpr() and
      call.getMethod() instanceof ProprietaryEvaluateMethod
    )
  }
}

/** Taint tracking step through request forwarding via a `RequestDispatcher`. */
private class RequestDispatcherTaintStep extends TaintTracking::AdditionalTaintStep {
  override predicate step(DataFlow::Node fromNode, DataFlow::Node toNode) {
    exists(
      RequestDispatcherForwardCall forwardCall, string attributeName, Parameter requestParameter,
      GetAttributeCall getAttributeCall
    |
      // Find the request parameter to the target of the `forward` call.
      requestParameter = forwardCall.getAPossibleServlet().getAHandlerMethod().getRequestParameter() and
      // Find flow from the parameter to the qualifier of a `GetAttributeCall(...)` call.
      DataFlow::localFlow(DataFlow::parameterNode(requestParameter),
        DataFlow::exprNode(getAttributeCall.getQualifier())) and
      // Find the name of the attribute accessed by the `GetAttributeCall(...)` call.
      // TODO there might not be a getAttribute call, it could just be a ${attribute} that goes through proprietaryEvaluate
      getAttributeCall.getAttributeName() = attributeName and
      // Add flow from the expression set as the value of the attribute to the `GetAttributeCall(...)` call.
      fromNode.asExpr() = forwardCall.getASetAttributeValue(attributeName) and
      toNode.asExpr() = getAttributeCall
    )
  }
}

class GetAttributeCall extends MethodAccess {
  GetAttributeCall() { getMethod() instanceof ServletRequestGetAttributeMethod }

  /**
   * Gets the name of the attribute which is returned by this call, assuming it is specified as a
   * compile time constant.
   */
  string getAttributeName() {
    exists(CompileTimeConstantExpr c |
      DataFlow::localFlow(DataFlow::exprNode(c), DataFlow::exprNode(getArgument(0))) and
      result = c.getStringValue()
    )
  }
}

class ServletClassExt extends ServletClass {
  /** Gets a method on this class that handles requests. */
  HandlerMethod getAHandlerMethod() { result = getAMethod() }
}

abstract class HandlerMethod extends Method {
  Parameter getRequestParameter() {
    result = getAParameter() and
    result.getType() instanceof HttpServletRequest
  }
}

class DoMethod extends HandlerMethod {
  DoMethod() { getName().matches("do%") }
}

/** The service method on a class generated from JSP. */
class JspServiceMethod extends HandlerMethod {
  JspServiceMethod() { hasName("_jspService") }
}

/** An annotation of type `WebServlet`, whose `value` element is a servlet path. */
class WebServletAnnotation extends Annotation {
  WebServletAnnotation() { getType().hasName("WebServlet") }

  string getPath() { result = getValue("value").(StringLiteral).getValue() }
}

/** A call to a method named `getRequestDispatcher`. This may be on either a `ServletContext` or an `HttpServletRequest`. */
class GetRequestDispatcherCall extends MethodAccess {
  GetRequestDispatcherCall() { getMethod() instanceof GetRequestDispatcherMethod }

  /** Gets the path of a resource wrapped by the returned dispatcher. */
  string getAServletName() {
    exists(CompileTimeConstantExpr ce |
      ce.getStringValue() = result and
      DataFlow::localFlow(DataFlow::exprNode(ce), DataFlow::exprNode(getArgument(0)))
    )
  }

  /** Gets a `Servlet` class wrapped by the returned dispatcher. */
  ServletClassExt getAPossibleServlet() {
    // A servlet with a web servlet annotation for the given resource path.
    result.getAnAnnotation().(WebServletAnnotation).getPath() = getAServletName()
    or
    // A JSP generated servlet for the given resource path.
    // TODO: This only matches on the basename, not the full path.
    // To be more robust, work out the path of each JSP file starting from WEB-INF.
    exists(string jspFileName |
      getAServletName().regexpCapture(".*/([^/]*)", 1) = jspFileName and
      result.getName() = getGeneratedJspJavaClassName(jspFileName)
    )
  }

  RequestDispatcherForwardCall getForward() {
    DataFlow::localFlow(DataFlow::exprNode(this), DataFlow::exprNode(result.getQualifier()))
  }
}

/** A call to `javax.servlet.RequestDispatcher.forward(request, response)`. */
class RequestDispatcherForwardCall extends MethodAccess {
  RequestDispatcherForwardCall() { getMethod() instanceof RequestDispatcherForwardMethod }

  /** Gets a call to `setAttribute` on the `request` object passed to this `forward` call. */
  MethodAccess getASetAttributeCall() {
    result.getMethod() instanceof ServletRequestSetAttributeMethod and
    DataFlow::localFlow(DataFlow::exprNode(result.getQualifier()),
      DataFlow::exprNode(getArgument(0)))
  }

  /** Gets a `Servlet` class wrapped by the `RequestDispatcher` used in this `forward` call. */
  ServletClassExt getAPossibleServlet() {
    exists(GetRequestDispatcherCall rd |
      rd.getForward() = this and
      result = rd.getAPossibleServlet()
    )
  }

  /** Gets an `Expr` set as the value for the attribute with `name` prior to `this` call to `forward`. */
  Expr getASetAttributeValue(string name) {
    exists(MethodAccess setAttributeCall, CompileTimeConstantExpr c |
      DataFlow::localFlow(DataFlow::exprNode(c), DataFlow::exprNode(setAttributeCall.getArgument(0))) and
      setAttributeCall = getASetAttributeCall() and
      name = c.getStringValue() and
      result = setAttributeCall.getArgument(1)
    )
  }
}

/** Gets the name of the generated Java class for the JSP file at `jspFileName`. */
bindingset[jspFileName]
string getGeneratedJspJavaClassName(string jspFileName) {
  // x.jsp -> x_jsp
  exists(string stem |
    jspFileName = stem + ".jsp" and
    result = stem + "_jsp"
  )
}

/** The class `javax.servlet.jsp.JspContext`. */
class JspContext extends RefType {
  JspContext() { this.hasQualifiedName("javax.servlet.jsp", "JspContext") }
}

/** The method `javax.servlet.jsp.JspContext.getOut()`. */
class JspContextGetOutMethod extends Method {
  JspContextGetOutMethod() {
    this.getDeclaringType() instanceof JspContext and
    this.hasName("getOut")
  }
}

/**
 * A call that writes its argument to a JSP writer.
 * Any content written to a JSP page goes through
 * such a call in the generated Java code.
 */
class JspWrite extends MethodAccess {
  JspWrite() {
    exists(MethodAccess getOutCall, string name |
      // JspContext.getOut() is used to obtain a writer.
      getOutCall = any(JspContextGetOutMethod m).getAReference() and
      // The writer is within the service method generated for a JSP page.
      getOutCall.getEnclosingCallable() instanceof JspServiceMethod and
      // The writer is used as the qualifier of this call.
      DataFlow::localFlow(DataFlow::exprNode(getOutCall), DataFlow::exprNode(this.getQualifier())) and
      // This call is to a write method on the writer.
      this.getMethod().hasName(name) and
      (name = "write" or name = "print")
    )
  }
}

/** 
 * Content written to a JSP page.
 * TODO: associated with JspGeneratedClass.
 */
newtype TJspContent = 
TJspConstantContent(CompileTimeConstantExpr e) {
  e instanceof JspWrittenContent
}
or
TJspExpressionLanguageContent(MethodAccess proprietaryEvaluateCall, CompileTimeConstantExpr e) {
  proprietaryEvaluateCall.getMethod() instanceof ProprietaryEvaluateMethod and
  TaintTracking::localTaint(DataFlow::exprNode(proprietaryEvaluateCall), DataFlow::exprNode(any(JspWrittenContent c))) and
  e = proprietaryEvaluateCall.getArgument(0)
}
or
TJspJavaStatement(Stmt s) {
  s = any(JspGeneratedClass c).getAWrittenStatement() and
  not s = any(JspWrittenContent content).getEnclosingStmt()
}


class JspWrittenContent extends Expr {
  JspWrittenContent() {
    this = any(JspWrite write).getAnArgument()
  }
}

/** A class generated from a JSP page. */
class JspGeneratedClass extends Class {
  JspGeneratedClass() {
    this.getName().matches("%_jsp")
  }

  JspServiceMethod getServiceMethod() {
    result = this.getAMethod()
  }

  JspWrite getAWrite() {
    result.getEnclosingCallable() = this.getServiceMethod()
  }

  JspWrite getFirstWrite() {
    // We assume that the first element on the page is the opening <html> tag.
    // This implies the generated code for the page content starts with a write call
    // rather than Java that is embedded on the page.
    result = min(JspWrite write | write = this.getAWrite() | write order by write.getLocation().getStartLine())
  }

  JspWrite getLastWrite() {
    // We assume that the last element on the page is the closing </html> tag.
    // This implies the generated code for the page content ends with a write call
    // rather than Java that is embedded on the page.
    result = max(JspWrite write | write = this.getAWrite() | write order by write.getLocation().getStartLine())
  }

  predicate generatedLineRange(int start, int end) {
    start = this.getFirstWrite().getLocation().getStartLine() and
    end = this.getLastWrite().getLocation().getEndLine()
  }

  Stmt getAWrittenStatement() {
    exists(int start, int end |
      this.generatedLineRange(start, end) and
      result.getEnclosingCallable() = this.getServiceMethod() and
      start <= result.getLocation().getStartLine() and
      end >= result.getLocation().getEndLine()
    )
  }

  int getNumberOfLinesSpanned(TJspContent c) {
    exists(CompileTimeConstantExpr e |
      c = TJspConstantContent(e) and
      result = count(e.getStringValue().indexOf("\n")) + 1
    )
    or
    c = TJspExpressionLanguageContent(_, _) and
    result = 1 // assumes attribute expressions cannot span multiple lines
    or
    exists(Stmt s |
      c = TJspJavaStatement(s) and
      result = s.getTotalNumberOfLines()
    )
  }
}


