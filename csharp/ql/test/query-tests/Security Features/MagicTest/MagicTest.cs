using System;
namespace X
{
	public class Y
	{
		public string A => "A";
		public string B => "B";
		public string C => "C";
		public string D => "D";
		
		public static void test() {
			var obj = new Y();
			Console.WriteLine(obj.A);
		}
	}
}