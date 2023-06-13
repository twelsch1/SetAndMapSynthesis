package bcs.programNode;

import java.util.ArrayList;
import java.util.HashSet;

import bcs.datatypes.IntData;
import bcs.utils.Utils;

public abstract class Node {
	public Node children[];

	public StringBuilder makeLispTree(StringBuilder buf) {
		if (children.length == 0)
			return buf.append(toString());
		else {
			buf.append("(");
			buf.append(toString());
			for (int x = 0; x < children.length; x++) {
				buf.append(" ");
				children[x].makeLispTree(buf);
			}
			buf.append(")");
			return buf;
		}
	}

	public String makeLispTree() {
		return makeLispTree(new StringBuilder()).toString();
	}
		
	public abstract String getNodeType();

	public abstract String toString();
	
	//syntactic sugar allowing direct evaluation given variables, with IntData created inside.
	public int evaluate(int[] variables) {
		IntData id = new IntData();
		this.eval(id, variables);
		return id.x;
	}
	
	public ArrayList<String> extractPossibleIntProgramsPlusMinusOne() {
		ArrayList<String> retVal = new ArrayList<>();
		
		HashSet<String> uniquePrograms = extractPossibleIntPrograms(new HashSet<String>());
		for (String s : uniquePrograms) {
			retVal.add(s);
			retVal.add("(+ 1 " + s + ")");
			retVal.add("(- " + s + " 1)");

		}
		
		return retVal;
	}
	
	public HashSet<String> extractPossibleIntPrograms(HashSet<String> listSoFar) {
		if (this.getNodeType().equals("int")) {
			listSoFar.add(this.makeLispTree());
		} else {
			for (int i = 0; i < this.children.length; i++) {
				listSoFar.addAll(children[i].extractPossibleIntPrograms(listSoFar));
			}
		}
		
		return listSoFar;
	}

	public abstract void eval(final IntData input, final int[] variables);
	
	//Ensures that the program is in the correct format to build node from i.e. just one space between functions
	//and children, children and each other.

	
	public static String formatProgramStringForNode(String program) {
		return program.replaceAll("\\s{2,}", " ").trim().replaceAll("\\(\s+", "(").replaceAll("\s+\\)", ")");
		//return program.replaceAll("\\(\s+", "(").replaceAll("\\s{2,}\\)", ")").replaceAll("\\s{2,}", " ").trim();
	}
	
	public static Node buildNodeFromProgramString(String program) {
		return buildNodeFromProgramString(program,null);
	}

	public static Node buildNodeFromProgramString(String program, HashSet<String> definedFunctions) {


		Node node = null;
		//gets the function operator and/or the constant/variable
		String funcType = Utils.scanToSpace(program);
		
		//System.out.println(funcType);
		int numChildren = 0;
		

		//create node as the type prescribed by funcType and determine number of children
		
		//OK, so for and+or+xor, rather than hardcoding as 2 children, extract functions until we reach the closing parentheses, and then we have
		//that as our number of children. Note: This breaks evaluation, it is only used for directProgramExtraction. Should maybe
		//have a safe and unsafe version.
		if (funcType.equals("(+")) {
			node = new Add();
			numChildren = 2;
		} else if (funcType.equals("(-")) {
			node = new Sub();
			numChildren = 2;
		} else if (funcType.equals("(*")) {
			node = new Mul();
			numChildren = 2;
		} else if (funcType.equals("(ite")) {
			node = new ITE();
			numChildren = 3;
		} else if (funcType.equals("(and")) {
			node = new And();
			numChildren = Node.countChildren(program, funcType.length() + 1);
		} else if (funcType.equals("(or")) {
			node = new Or();
			numChildren = Node.countChildren(program, funcType.length() + 1);
		} 
		else if (funcType.equals("(xor")) {
			node = new XOR();
			numChildren = Node.countChildren(program, funcType.length() + 1);
		} 
		else if(funcType.equals("(=>")) {
			node = new Implies();
			numChildren = 2;
		}
		else if (funcType.equals("(not")) {
			node = new Not();
			numChildren = 2;
		} else if (funcType.equals("(=")) {
			node = new Equals();
			numChildren = 2;
		} else if (funcType.equals("(distinct")) {
			node = new Distinct();
			numChildren = 2;
		} else if (funcType.equals("(>")) {
			node = new GT();
			numChildren = 2;
		} else if (funcType.equals("(>=")) {
			node = new GTE();
			numChildren = 2;
		} else if (funcType.equals("(<")) {
			node = new LT();
			numChildren = 2;
		} else if (funcType.equals("(<=")) {
			node = new LTE();
			numChildren = 2;
		} else if (funcType.contains("var")) {
			//extract the index out, always var number subtracted by 1 to get to 0 indexing
			int idx = Integer.parseInt(funcType.substring(3,funcType.length()-1)) - 1;
			node = new Var(funcType, idx);
		} else if (funcType.equals("true")) {
			node = new EphemeralBoolean(1);
		} else if (funcType.equals("false")) {
			node = new EphemeralBoolean(0);
		} else if (definedFunctions != null && funcType.length() > 1 && definedFunctions.contains(funcType.substring(1))) {
			String function = funcType.substring(1);
			String type = "int";
			if (function.equals("iteB") || function.equals("or3") || function.equals("im")) {
				type = "boolean";
			}
			node = new DefinedFunction(function, type);
			numChildren = Node.countChildren(program, funcType.length() + 1);
		} else {
			node = new Ephemeral(Integer.parseInt(funcType));
		}

		//set node's child list to be number of children;
		node.children = new Node[numChildren];

		//use to move up in the string past this function onto its children
		int idx = funcType.length() + 1;
		for (int i = 0; i < numChildren; i++) {
			//extract the next function and then call recursively, then move the index up length of that function plus 1 for the space
			String nextFunction = Utils.extractNextFunction(program.substring(idx));
			node.children[i] = buildNodeFromProgramString(nextFunction, definedFunctions);
			
			idx += nextFunction.length() + 1;
		}

		return node;
	}
	
	private static int countChildren(String function, int offset) {
		int idx = offset;
		int numChildren = 0;
		
		while (true) {
			String nextFunction = Utils.extractNextFunction(function.substring(idx));
			idx += nextFunction.length() +1;
			numChildren++;
			if (idx >= function.length()) {
				break;
			}
		}
		
		return numChildren;
		
	}

	/*
	public static void main(String[] args) {
		String program = "(and (>= 2 var2;)    (>= 0 var2;) (= (+ var1; 1)\n var3;)"
				+ "    "
				+ ")  ";
		System.out.println(program);
		int[] variables = {3, 1, 4};
		Node node = Node.buildNodeFromProgramString(Node.formatProgramStringForNode(program));
		System.out.println(node.makeLispTree());

		System.out.println(node.evaluate(variables));

		ArrayList<String> fullExtractionList = node.extractPossibleIntProgramsPlusMinusOne();
		
		for (String s : fullExtractionList) {
			System.out.println(s);
		}
		
	}*/

}
