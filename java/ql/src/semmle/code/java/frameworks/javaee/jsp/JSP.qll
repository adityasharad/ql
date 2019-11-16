/** Classes and predicates to model JavaServer Pages (JSP) and the associated generated code. */

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

/** A call to `org.apache.jasper.runtime.PageContextImpl.proprietaryEvaluate`. */
class ProprietaryEvaluateCall extends MethodAccess {
  ProprietaryEvaluateCall() { getMethod() instanceof ProprietaryEvaluateMethod }

  /** Gets the EL string literal of the form `${...}` that is evaluated by this call. */
  StringLiteral getEvaluatedArgument() { result = this.getArgument(0) }

  /** Gets the named EL expression that is evaluated by this call. */
  string getEvaluatedAttributeName() {
    this.getEvaluatedArgument().getValue() = "${" + result + "}"
  }
}

/** A reference to a JSP include parameter, as a source of remote user input. */
class JspParamFlowSource extends RemoteFlowSource {
  Generated::ExpressionLanguageExpr e;

  JspParamFlowSource() {
    this.asExpr() = e and
    e.getExpressionLanguageString().getStringValue().matches("${param.%}%")
  }

  override string getSourceType() { result = "JSP parameter" }
}

module JspTaintSteps {
  private newtype TUnit = TMkUnit()

  private class Unit extends TUnit {
    string toString() { result = "unit" }
  }

  /**
   * STUB: This should be removed when using CodeQL 1.23 and later.
   * A unit class for adding additional taint steps.
   *
   * Extend this class to add additional taint steps that should apply to all
   * taint configurations.
   */
  class AdditionalTaintStep extends Unit {
    /**
     * Holds if the step from `node1` to `node2` should be considered a taint
     * step for all configurations.
     */
    abstract predicate step(DataFlow::Node node1, DataFlow::Node node2);
  }

  /** Taint tracking step from `x` to `org.apache.jasper.runtime.PageContextImpl.proprietaryEvaluate(x)`. */
  private class JspProprietaryEvaluateTaintStep extends AdditionalTaintStep {
    override predicate step(DataFlow::Node source, DataFlow::Node target) {
      exists(ProprietaryEvaluateCall call |
        call.getEvaluatedArgument() = source.asExpr() and
        call = target.asExpr()
      )
    }
  }

  /** Taint tracking step through request forwarding via a `RequestDispatcher`. */
  private class RequestDispatcherTaintStep extends AdditionalTaintStep {
    override predicate step(DataFlow::Node fromNode, DataFlow::Node toNode) {
      exists(
        RequestDispatcherForwardCall forwardCall, string attributeName, Parameter requestParameter,
        JspAttributeRead attributeRead, Expr attributeWrite
      |
        // Find the request parameter of the target of the `forward` call.
        requestParameter = forwardCall
              .getAPossibleServlet()
              .getAHandlerMethod()
              .getRequestParameter() and
        // Find where an attribute of the request parameter is read.
        requestParameter = attributeRead.getRequestParameter() and
        // Find the name of the attribute that is read.
        attributeRead.getAttributeName() = attributeName and
        // Find where the same attribute is written before the forward call.
        attributeWrite = forwardCall.getASetAttributeValue(attributeName) and
        // Add flow from the write to the read.
        fromNode.asExpr() = attributeWrite and
        toNode.asExpr() = attributeRead
      )
    }
  }
}

private class JspAttributeRead extends Expr {
  Parameter requestParameter;
  string attributeName;

  JspAttributeRead() {
    exists(GetAttributeCall getAttributeCall | getAttributeCall = this |
      DataFlow::localFlow(DataFlow::parameterNode(requestParameter),
        DataFlow::exprNode(getAttributeCall.getQualifier())) and
      getAttributeCall.getAttributeName() = attributeName
    )
    or
    exists(ProprietaryEvaluateCall proprietaryEvaluateCall | proprietaryEvaluateCall = this |
      requestParameter = proprietaryEvaluateCall
            .getEnclosingCallable()
            .(JspServiceMethod)
            .getAParameter() and
      proprietaryEvaluateCall.getEvaluatedAttributeName() = attributeName
    )
  }

  Parameter getRequestParameter() { result = requestParameter }

  string getAttributeName() { result = attributeName }
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
bindingset[result]
string getGeneratedJspJavaClassName(string jspFileName) {
  // TODO: Use more principled heuristics based on the directory structure, not just the filename.
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

/** A data flow node that corresponds to a location in JSP code. */
class JspDataFlowNode extends DataFlow::Node {
  Raw::JspElement jspElement;
  Generated::JavaElement javaElement;

  JspDataFlowNode() {
    (
      this.asExpr() = javaElement or
      this.(DataFlow::PostUpdateNode).getPreUpdateNode().asExpr() = javaElement
      // Not needed yet: at time of writing, no JavaElements are Parameters.
      // or this.asParameter() = javaElement
    ) and
    jspElement.getGeneratedCode() = javaElement
  }

  override predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    jspElement.hasLocationInfo(path, sl, sc, el, ec)
  }
}

class JspFile extends File {
  JspFile() { this.getExtension() = "jsp" }
}

/** Models elements in raw JSP source. */
private module Raw {
  private newtype TJspElement =
    THtmlContent(Generated::HtmlContent c) or
    TExpressionLanguageExpr(Generated::ExpressionLanguageExpr c) or
    TExpression(Generated::Expression e) or
    TScriptletStmt(Generated::ScriptletStmt s)

  /**
   * Content written to a JSP page.
   */
  class JspElement extends TJspElement {
    abstract string toString();

    predicate hasLocationInfo(string filePath, int startLine, int startCol, int endLine, int endCol) {
      exists(JspFile file, string javaClassName, string jspFileName |
        this
            .getGeneratedCode()
            .getWrittenStmt()
            .getEnclosingCallable()
            .getDeclaringType()
            .hasName(javaClassName) and
        javaClassName = getGeneratedJspJavaClassName(jspFileName) and
        jspFileName = file.getBaseName() and
        filePath = file.getAbsolutePath()
      ) and
      startLine = this.getStartLine() and
      endLine = this.getEndLine() + 1 and
      // It is possible to compute narrower locations by keeping track of the
      // start and end column positions of each element in sequence.
      // This is error-prone because of variations in whitespace and JSP tags.
      // For simplicity, just report locations at the start of the line.
      startCol = 1 and
      endCol = 0 // A large end col flows onto later lines in QL for Eclipse.
    }

    final int getStartLine() {
      result =
        // The number of lines spanned by all preceding written statements
        // in the same generated class.
        // TODO: this is quadratic, performance can be improved.
        sum(Generated::JavaElement prevElement, Generated::JspWrittenStmt prevStmt |
            prevStmt = this.getGeneratedCodeStmt().getGeneratedClass().getAWrittenStatement() and
            prevStmt.getWrittenStmtRank() < this.getGeneratedCodeStmt().getWrittenStmtRank() and
            prevElement.getWrittenStmt() = prevStmt
          |
            prevElement.getEndLineRelativeOffset()
          ) +
          // 1-based
          1
    }

    final int getEndLine() {
      result = this.getStartLine() + this.getGeneratedCode().getEndLineRelativeOffset()
    }

    abstract Generated::JavaElement getGeneratedCode();

    final Generated::JspWrittenStmt getGeneratedCodeStmt() {
      result = this.getGeneratedCode().getWrittenStmt()
    }
  }

  class HtmlContent extends JspElement, THtmlContent {
    Generated::HtmlContent c;

    HtmlContent() { this = THtmlContent(c) }

    override string toString() { result = "JSP HTML content" }

    override Generated::HtmlContent getGeneratedCode() { result = c }
  }

  class Expression extends JspElement, TExpression {
    Generated::Expression e;

    Expression() { this = TExpression(e) }

    override string toString() { result = "JSP expression" }

    override Generated::Expression getGeneratedCode() { result = e }
  }

  class ExpressionLanguageExpr extends JspElement, TExpressionLanguageExpr {
    Generated::ExpressionLanguageExpr e;

    ExpressionLanguageExpr() { this = TExpressionLanguageExpr(e) }

    override string toString() { result = "JSP EL expression" }

    override Generated::ExpressionLanguageExpr getGeneratedCode() { result = e }
  }

  class ScriptletStmt extends JspElement, TScriptletStmt {
    Generated::ScriptletStmt s;

    ScriptletStmt() { this = TScriptletStmt(s) }

    override string toString() { result = "JSP scriptlet statement" }

    override Generated::ScriptletStmt getGeneratedCode() { result = s }
  }
}

predicate test(Raw::JspElement c, Generated::JavaElement e) { c.getGeneratedCode() = e }

/**
 * Models Java elements generated by compiling raw JSP source.
 *
 * Known correspondence between JSP and generated Java, when JSP is compiled by Tomcat and the Jetty JSPC Maven plugin:
 * - Regular HTML turns into string literals written to the JspWriter.
 *   e.g. `<html>\n<body>...` becomes `out.write("<html>\n<body>...");`
 *   Note that multiple successive lines of HTML may be combined into a single string.
 * - JSP Expression Language includes turn into string literals passed to proprietaryEvaluate and then the JspWriter.
 *   e.g. `${param.id}` becomes `out.write((String) proprietaryEvaluate("${param.id}", ...));`
 * - JSP scriptlets are fragments of Java code (statements). These are preserved as statements in the generated code (note that scriptlets may be interspersed with non-scriptlet tags.)
 *   e.g.`<% String p = request.getParameter("p"); %>` becomes `String p = request.getParameter("p");`.
 * - JSP expressions are preserved as expressions in the generated code, which are printed to the JspWriter.
 *   e.g. `<%= attribute %>` becomes `out.print( attribute );`
 * - [Not supported] JSP directives and includes
 */
private module Generated {
  /** A generated Java source code element that directly corresponds to a JSP element. */
  abstract class JavaElement extends Top {
    JspWrittenStmt writtenStmt;

    final JspWrittenStmt getWrittenStmt() { result = writtenStmt }

    /** Gets the difference between the 1-based inclusive end and start lines of the corresponding JSP element. */
    abstract int getEndLineRelativeOffset();
  }

  class HtmlContent extends JavaElement, CompileTimeConstantExpr, JspWrittenContent {
    HtmlContent() { writtenStmt = this.getEnclosingStmt() }

    override int getEndLineRelativeOffset() { result = count(this.getStringValue().indexOf("\n")) }
  }

  class ExpressionLanguageExpr extends JavaElement, Expr {
    CompileTimeConstantExpr elString;
    MethodAccess proprietaryEvaluateCall;
    JspWriteCall writeCall;

    ExpressionLanguageExpr() {
      writtenStmt = this.getEnclosingStmt() and
      proprietaryEvaluateCall.getMethod() instanceof ProprietaryEvaluateMethod and
      elString = proprietaryEvaluateCall.getArgument(0) and
      // This element is the argument of `write`, not the constant string.
      // Doing so allows this element to be identified as an XSS sink.
      this = writeCall.getAnArgument() and
      // The `proprietaryEvaluate` call flows into the argument of `write`.
      DataFlow::localFlow(DataFlow::exprNode(proprietaryEvaluateCall), DataFlow::exprNode(this))
    }

    CompileTimeConstantExpr getExpressionLanguageString() { result = elString }

    override int getEndLineRelativeOffset() {
      // assumes these are never multiline
      result = 0
    }
  }

  /** A Java expression generated from JSP `<%= ... %>` expression syntax. */
  class Expression extends JavaElement, JspWrittenContent {
    Expression() {
      writtenStmt = this.getEnclosingStmt() and
      // Assumes that expression syntax isn't used to store constants.
      this = any(JspPrintCall write).getAnArgument() and
      // Exclude EL expressions: those are modelled separately.
      not exists(ProprietaryEvaluateMethod m |
        DataFlow::localFlow(DataFlow::exprNode(m.getAReference()), DataFlow::exprNode(this))
      )
    }

    override int getEndLineRelativeOffset() {
      // Assume a single line.
      result = 0
      // result = this.getLocation().getNumberOfLines() - 1
    }
  }

  /** A Java statement generated from JSP `<% ... %>` scriptlet syntax. */
  class ScriptletStmt extends JavaElement, JspWrittenStmt {
    ScriptletStmt() {
      writtenStmt = this and
      // Not one of the `out.write/print` calls, but a regular Java statement within the same block.
      not this = any(JspWriterCall w).getEnclosingStmt()
    }

    override int getEndLineRelativeOffset() { result = this.getLocation().getNumberOfLines() - 1 }
  }

  class JspWrittenContent extends Expr {
    JspWrittenContent() { this = any(JspWriterCall write).getAnArgument() }
  }

  class JspConstantWrittenContent extends JspWrittenContent, CompileTimeConstantExpr { }

  class JspWrittenStmt extends Stmt {
    JspGeneratedClass c;

    JspWrittenStmt() { this = c.getAWrittenStatement() }

    JspGeneratedClass getGeneratedClass() { result = c }

    /**
     * Gets the 1-based index of this JSP statement in the sequence of all JSP statements in the
     * same generated servlet method.
     */
    int getWrittenStmtRank() {
      this = rank[result](JspWrittenStmt s |
          s = c.getAWrittenStatement()
        |
          s order by s.getLocation().getStartLine()
        )
    }

    /** Gets a constant expression written in this statement, if any. */
    JspConstantWrittenContent getWrittenConstant() { result.getEnclosingStmt() = this }
  }

  /**
   * A call that writes its argument to a JSP writer.
   * Any HTML or JSP EL content written to a JSP page goes through
   * such a call in the generated Java code.
   */
  class JspWriterCall extends MethodAccess {
    JspWriterCall() {
      exists(MethodAccess getOutCall, string name |
        // JspContext.getOut() is used to obtain a writer.
        getOutCall = any(JspContextGetOutMethod m).getAReference() and
        // The writer is within the service method generated for a JSP page.
        getOutCall.getEnclosingCallable() instanceof JspServiceMethod and
        // The writer is used as the qualifier of this call.
        DataFlow::localFlow(DataFlow::exprNode(getOutCall), DataFlow::exprNode(this.getQualifier())) and
        // This call is to a write or print method on the writer.
        this.getMethod().hasName(name) and
        (name = "write" or name = "print")
      )
    }
  }

  class JspWriteCall extends JspWriterCall {
    JspWriteCall() { this.getMethod().hasName("write") }
  }

  class JspPrintCall extends JspWriterCall {
    JspPrintCall() { this.getMethod().hasName("print") }
  }

  /** A class generated from a JSP page. */
  class JspGeneratedClass extends Class {
    JspServiceMethod serviceMethod;

    JspGeneratedClass() { this.getName().matches("%_jsp") and serviceMethod = this.getAMethod() }

    JspServiceMethod getServiceMethod() { result = serviceMethod }

    JspWriterCall getAWrite() { result.getEnclosingCallable() = this.getServiceMethod() }

    JspWriterCall getFirstWrite() {
      // We assume that the first element on the page is the opening <html> tag.
      // This implies the generated code for the page content starts with a write call
      // rather than Java that is embedded on the page.
      result = min(JspWriterCall write |
          write = this.getAWrite()
        |
          write order by write.getLocation().getStartLine()
        )
    }

    JspWriterCall getLastWrite() {
      // We assume that the last element on the page is the closing </html> tag.
      // This implies the generated code for the page content ends with a write call
      // rather than Java that is embedded on the page.
      result = max(JspWriterCall write |
          write = this.getAWrite()
        |
          write order by write.getLocation().getStartLine()
        )
    }

    /**
     * Holds if the statements that write the JSP content for this generated class lie on lines
     *     `[start..end]` (1-based, inclusive) of the class.
     */
    private predicate generatedLineRange(int start, int end) {
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
  }
}
