/**
 * @kind problem
 * @id id
 */
import java
import semmle.code.java.frameworks.javaee.jsp.JSP

// query
predicate q = JspGeneratedCode::testFile/2;

// query
predicate classes(Class c, string name) {
  name = c.getName()
}

query
predicate files(File c, string name) {
  name = c.getBaseName()
}