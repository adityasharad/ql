<html>
<body>
  <!-- JSL EL accessing the id field of the param object. -->
  <input value="${param.id}"></input>
  <!-- JSP scriptlet accessing a request attribute, in a complete statement. -->
  <% String attribute = (String)request.getAttribute("param"); %>
  <!-- JSP expression accessing the value of a variable. -->
  <span><%= attribute %></span>

  <!-- JSP scriptlet interspersed with HTML and EL. -->
  <% for(int i = 0; i < 3; i++) { %>
    <p>Current value is <%= i %>.</p>
  <% } %>
  }
</body>
</html>