// Test case for
// CWE-079: Improper Neutralization of Input During Web Page Generation ('Cross-site Scripting')
// http://cwe.mitre.org/data/definitions/79.html
// involving Java Server Pages (JSP).

package test.cwe079.cwe.examples;

import java.io.IOException;
import javax.servlet.ServletException;
import javax.servlet.http.Cookie;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.RequestDispatcher;

public class XssJsp extends HttpServlet {
	public void getData(HttpServletRequest request, HttpServletResponse response) throws Exception {
		String param = (String)request.getParameter("param");
		param = param.trim();
		request.setAttribute("param", param);

		// request.getRequestDispatcher("/WEB-INF/jsp/service/getData.jsp").forward(request, response);
		request.getRequestDispatcher("/XssJsp.jsp").forward(request, response);
	}
}
