<html>
<body>
  <!-- Use of the param object. -->
  <input value="${param.id}"></input>
  
  <!-- Use of a request attribute. -->
  <% String attribute = (String)request.getAttribute("param"); %>
  <span><%= attribute %></span>
</body>
</html>