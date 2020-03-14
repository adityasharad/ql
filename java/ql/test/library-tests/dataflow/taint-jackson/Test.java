import java.io.FileInputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.ObjectWriter;

class Test {
	public static String taint() { return "tainted"; }

	
	public static void jackson() {
		String s = taint();
		ObjectMapper om = new ObjectMapper();
		File file = new File("testFile");
		om.writeValue(file, s);
		OutputStream out = new OutputStream(); // TODO how to construct this?
		om.writeValue(out, s);
		Writer writer = new Writer(); // TODO how to construct this?
		om.writeValue(writer, s);
		String t = om.writeValueAsString(s);
		bytes[] bs = om.writeValueAsBytes(s);
		String reconstructed = new String(bs, "utf-8");
	}
}
