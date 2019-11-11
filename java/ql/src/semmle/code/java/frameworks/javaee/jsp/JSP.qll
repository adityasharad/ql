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
bindingset[result]
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

module JspGeneratedCode {
  // Known correspondence between JSP and generated Java, when JSP is compiled by Tomcat and the Jetty JSPC Maven plugin:
  // - Regular HTML turns into string literals written to the JspWriter.
  //   e.g. `<html>\n<body>...` becomes `out.write("<html>\n<body>...");`
  //   Note that multiple successive lines of HTML may be combined into a single string.
  // - JSP Expression Language includes turn into string literals passed to proprietaryEvaluate and then the JspWriter.
  //   e.g. `${param.id}` becomes `out.write((String) proprietaryEvaluate("${param.id}", ...));
  // - JSP scriptlets are fragments of Java code (statements). These are preserved as statements in the generated code (note that scriptlets may be interspersed with non-scriptlet tags.)
  //   e.g.`<% String p = request.getParameter("p"); %>` becomes `String p = request.getParameter("p");`.
  // - JSP expressions are preserved as expressions in the generated code, which are printed to the JspWriter.
  //   e.g. `<%= attribute %>` becomes `out.print( attribute );`
  // - [Not supported] JSP directives
  predicate testLoc(JspHtmlContent c, Expr e) { c.getGeneratedCode() = e }

  predicate testFile(File f, string name) {
    f.getExtension() = "jsp" and
    name = f.getBaseName()
  }

  /**
   * A call that writes its argument to a JSP writer.
   * Any HTML or JSP EL content written to a JSP page goes through
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
        // This call is to a write or print method on the writer.
        this.getMethod().hasName(name) and
        (name = "write" or name = "print")
      )
    }
  }

  /**
   * Content written to a JSP page.
   */
  private newtype TJspContent =
    TJspHtmlContent(Generated::HtmlContent c) or
    TJspExpressionLanguageExpr(Generated::ExpressionLanguageExpr c) or
    TJspExpression(Generated::Expression e) or
    TJspScriptletStmt(Generated::ScriptletStmt s)


  predicate test(JspContent c, Generated::JavaElement e, int i) {
    c.getStartColumn() = i and
    c.getGeneratedCode() = e
  }

  abstract class JspContent extends TJspContent {
    abstract string toString();

    predicate hasLocationInfo(string filePath, int startLine, int startCol, int endLine, int endCol) {
      // TODO
      filePath = "C:/semmle/code/ql/java/ql/test/query-tests/security/CWE-079/semmle/tests/maven-project/src/main/webapp/XssJsp.jsp" and
      startLine = this.getStartLine() and
      startCol = this.getStartColumn() and
      endLine = this.getEndLine() and
      endCol = this.getEndColumn()
    }

    // TODO Fix locations
    // span length for expressions (both kinds)
    // account for the <% and %> on either side

    final int getStartLine() {
      result =
        // The number of lines spanned by all preceding written statements
        // in the same generated class.
        sum(Generated::JavaElement prevElement, JspWrittenStmt prevStmt |
            prevStmt = this.getGeneratedCodeStmt().getGeneratedClass().getAWrittenStatement() and
            prevStmt.getWrittenStmtRank() < this.getGeneratedCodeStmt().getWrittenStmtRank() and
            prevElement.getWrittenStmt() = prevStmt
          |
            prevElement.getEndLineRelativeOffset()
          ) +
          // 1-based
          1
    }

   final int getStartColumn() {
      exists(int r | r = this.getGeneratedCodeStmt().getWrittenStmtRank() |
        // The first element starts at the beginning of the file.
        r = 1 and result = 1
        or
        // Otherwise, start where the previous element ends.
        r > 1 and
        exists(JspContent prevContent, JspWrittenStmt prevStmt |
          prevStmt = this.getGeneratedCodeStmt().getGeneratedClass().getAWrittenStatement() and
          prevStmt.getWrittenStmtRank() = r - 1 and
          prevContent.getGeneratedCodeStmt() = prevStmt and
          result = prevContent.getEndColumn() + 1
        )
      )
    }

    final int getEndLine() {
      result = this.getStartLine() + this.getGeneratedCode().getEndLineRelativeOffset()
    }

    final int getEndColumn() { result = this.getGeneratedCode().getLastLineLength() }

    abstract Generated::JavaElement getGeneratedCode();

    final JspWrittenStmt getGeneratedCodeStmt() {
      result = this.getGeneratedCode().getWrittenStmt()
    }

    final Location getGeneratedCodeLocation() { result = this.getGeneratedCode().getLocation() }
  }

  class JspHtmlContent extends JspContent, TJspHtmlContent {
    Generated::HtmlContent c;

    JspHtmlContent() { this = TJspHtmlContent(c) }

    override string toString() { result = "JSP HTML content: " + c.getStringValue() }

    override Generated::HtmlContent getGeneratedCode() { result = c }
  }

  class JspExpression extends JspContent, TJspExpression {
    Generated::Expression e;

    JspExpression() { this = TJspExpression(e) }

    override string toString() { result = "JSP expression: " + e.toString() }

    override Generated::Expression getGeneratedCode() { result = e }
  }

  class JspExpressionLanguageContent extends JspContent, TJspExpressionLanguageExpr {
    Generated::ExpressionLanguageExpr e;

    JspExpressionLanguageContent() { this = TJspExpressionLanguageExpr(e) }

    override string toString() { result = "JSP EL expression: " + e.toString() }

    override Generated::ExpressionLanguageExpr getGeneratedCode() { result = e }
  }

  class JspScriptletStmt extends JspContent, TJspScriptletStmt {
    Generated::ScriptletStmt s;

    JspScriptletStmt() { this = TJspScriptletStmt(s) }

    override string toString() { result = "JSP scriptlet statement: " + s.toString() }

    override Generated::ScriptletStmt getGeneratedCode() { result = s }
  }

  // or
  // TJspExpressionLanguageExpr(MethodAccess proprietaryEvaluateCall, CompileTimeConstantExpr e) {
  //   proprietaryEvaluateCall.getMethod() instanceof ProprietaryEvaluateMethod and
  //   TaintTracking::localTaint(DataFlow::exprNode(proprietaryEvaluateCall),
  //     DataFlow::exprNode(any(JspWrittenContent c))) and
  //   e = proprietaryEvaluateCall.getArgument(0)
  // } or
  // TJspJavaStatement(Stmt s) {
  //   s = any(JspGeneratedClass c).getAWrittenStatement() and
  //   not s = any(JspWrittenContent content).getEnclosingStmt()
  // }
  private module Generated {
    /** A generated Java source code element that directly corresponds to a JSP element. */
    abstract class JavaElement extends Top {
      JspWrittenStmt writtenStmt;

      final JspWrittenStmt getWrittenStmt() { result = writtenStmt }

      abstract int getEndLineRelativeOffset();

      abstract int getLastLineLength();
    }

    predicate testGenerated(JavaElement e, int endLineOffset, int endLineLength) {
      e.getEndLineRelativeOffset() = endLineOffset and
      e.getLastLineLength() = endLineLength
    }

    class HtmlContent extends JavaElement, CompileTimeConstantExpr, JspWrittenContent {
      HtmlContent() { writtenStmt = this.getEnclosingStmt() }

      override int getEndLineRelativeOffset() {
        result = count(this.getStringValue().indexOf("\n"))
      }

      override int getLastLineLength() {
        result = this.getStringValue().regexpFind("([^\n])+$", _, _).length()
      }
    }

    class ExpressionLanguageExpr extends JavaElement, CompileTimeConstantExpr {
      MethodAccess proprietaryEvaluateCall;

      ExpressionLanguageExpr() {
        // The `proprietaryEvaluate` call actually flows into the argument of `write`, but this is enough for now.
        writtenStmt = this.getEnclosingStmt() and
        proprietaryEvaluateCall.getMethod() instanceof ProprietaryEvaluateMethod and
        this = proprietaryEvaluateCall.getArgument(0)
      }

      override int getEndLineRelativeOffset() {
        // assumes these are never multiline
        result = 0
      }

      override int getLastLineLength() {
        // Assume a single line.
        result = this.getStringValue().length()
        // If these were multiline, we would have to use:
        // result = this.getStringValue().regexpFind("([^\n])+$", _, _).length()
      }
    }

    /** A Java expression generated from JSP `<%= ... %>` expression syntax. */
    class Expression extends JavaElement, JspWrittenContent {
      Expression() {
        writtenStmt = this.getEnclosingStmt() and
        // Assumes that expression syntax isn't used to store constants.
        // TODO: Remove this, and distinguish by looking for `out.print`.
        not this instanceof CompileTimeConstantExpr and
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

      override int getLastLineLength() {
        // Assume a single line.
        result = this.getLocation().getEndColumn() - this.getLocation().getStartColumn() + 1
      }
    }

    /** A Java statement generated from JSP `<% ... %>` scriptlet syntax. */
    class ScriptletStmt extends JavaElement, JspWrittenStmt {
      ScriptletStmt() {
        writtenStmt = this and
        // Not one of the `out.write/print` calls, but a regular Java statement within the same block.
        not this = any(JspWrite w).getEnclosingStmt()
      }

      override int getEndLineRelativeOffset() { result = this.getLocation().getNumberOfLines() - 1 }

      override int getLastLineLength() { result = this.getLocation().getEndColumn() }
    }
  }

  class JspWrittenContent extends Expr {
    JspWrittenContent() { this = any(JspWrite write).getAnArgument() }
  }

  class JspConstantWrittenContent extends JspWrittenContent, CompileTimeConstantExpr {
    int getNumberOfLinesSpanned() { result = count(this.getStringValue().indexOf("\n")) + 1 }

    int getLastLineLength() {
      result = this.getStringValue().regexpFind("([^\n])+$", _, _).length()
    }
  }

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

    /** Gets the number of lines spanned by this written statement in the original JSP. */
    int getNumberOfLinesSpanned() {
      if exists(this.getWrittenConstant())
      then result = count(this.getWrittenConstant().getStringValue().indexOf("\n")) + 1
      else result = this.getTotalNumberOfLines()
    }
  }

  /** A class generated from a JSP page. */
  class JspGeneratedClass extends Class {
    JspServiceMethod serviceMethod;

    JspGeneratedClass() { this.getName().matches("%_jsp") and serviceMethod = this.getAMethod() }

    JspServiceMethod getServiceMethod() { result = serviceMethod }

    JspWrite getAWrite() { result.getEnclosingCallable() = this.getServiceMethod() }

    JspWrite getFirstWrite() {
      // We assume that the first element on the page is the opening <html> tag.
      // This implies the generated code for the page content starts with a write call
      // rather than Java that is embedded on the page.
      result = min(JspWrite write |
          write = this.getAWrite()
        |
          write order by write.getLocation().getStartLine()
        )
    }

    JspWrite getLastWrite() {
      // We assume that the last element on the page is the closing </html> tag.
      // This implies the generated code for the page content ends with a write call
      // rather than Java that is embedded on the page.
      result = max(JspWrite write |
          write = this.getAWrite()
        |
          write order by write.getLocation().getStartLine()
        )
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
  }
}
