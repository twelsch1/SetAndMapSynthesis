package bcs.benchmark;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Scanner;

import bcs.multipleInvocation.MIUtils;
import bcs.programNode.Node;
import bcs.utils.Utils;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class Benchmark {

	private String functionName;
	private String assertionString;
	private String funString;
	private String[] variableNames;
	private String[] variableTypes;
	private String[] functionVariables;
	private String[] functionVariableTypes;
	private String[] synthesisVariableNames;
	private String[] definedFunctions;
	private String[] definedFunctionNames;
	private int[] constants;
	private ArrayList<ArrayList<String>> invocations;
	private String logic;

	public Benchmark(String functionName, String assertionString, String funString, String[] variableNames,
			String[] definedFunctions, String[] definedFunctionNames, String logic, ArrayList<ArrayList<String>> variances) {
		this.functionName = functionName;
		this.assertionString = assertionString;
		this.funString = funString;
		this.variableNames = variableNames;
		this.definedFunctions = definedFunctions;
		this.definedFunctionNames = definedFunctionNames;
		this.logic = logic;
		this.invocations = variances;
	}

	public String getFunctionName() {
		return functionName;
	}

	public String getAssertionString() {
		return assertionString;
	}

	public String getFunString() {
		return funString;
	}

	public String[] getVariableNames() {
		return variableNames;
	}

	public String[] getDefinedFunctions() {
		return definedFunctions;
	}

	public String[] getDefinedFunctionNames() {
		return definedFunctionNames;
	}
	
	public String getLogic() {
		return logic;
	}
	
	public ArrayList<ArrayList<String>> getInvocations() {
		return invocations;
	}
	
	public String[] getSynthesisVariableNames() {
		return synthesisVariableNames;
	}

	public void setSynthesisVariableNames(String[] synthesisVariableNames) {
		this.synthesisVariableNames = synthesisVariableNames;
	}
	
	

	public String[] getVariableTypes() {
		return variableTypes;
	}

	public void setVariableTypes(String[] variableTypes) {
		this.variableTypes = variableTypes;
	}

	public String[] getFunctionVariables() {
		return functionVariables;
	}

	public void setFunctionVariables(String[] functionVariables) {
		this.functionVariables = functionVariables;
	}

	public String[] getFunctionVariableTypes() {
		return functionVariableTypes;
	}

	public void setFunctionVariableTypes(String[] functionVariableTypes) {
		this.functionVariableTypes = functionVariableTypes;
	}

	public static Benchmark parseBenchmark(String filename) throws Exception {
		File file = new File(filename);
		String fileContent = Files.readString(file.toPath());
		
		
		
		//removes any space between ( and characters such that "( func " becomes "(func "
		fileContent = fileContent.replaceAll("\\(\s+", "(");
		//fileContent = fileContent.replaceAll("\s+\\)", ")");
		////System.out.println(fileContent);
		
		int[] constants = extractConstants(fileContent);
		
		ArrayList<String> subStrings = new ArrayList<>();

		int parenCounter = 0;
		String subString = "";
		for (int i = 0; i < fileContent.length(); i++) {
			subString += fileContent.charAt(i);
			if (fileContent.charAt(i) == '(') {
				parenCounter++;
			} else if (fileContent.charAt(i) == ')') {
				parenCounter--;
			}

			if (parenCounter == 0 && !subString.isBlank()) {
				subStrings.add(subString.strip());
				subString = "";
			}
		}

		String functionName = "";
		String funString = "";
		String logic = "";
		ArrayList<String> variables = new ArrayList<>();
		ArrayList<String> variableTypes = new ArrayList<>();
		ArrayList<String> functionVariables = new ArrayList<>();
		ArrayList<String> functionVariableTypes = new ArrayList<>();
		ArrayList<String> definedFunctions = new ArrayList<>();
		ArrayList<String> definedFunctionNames = new ArrayList<>();
		ArrayList<String> constraints = new ArrayList<>();
		for (String s : subStrings) {
			if (s.contains("set-logic")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // it's directly after synth-fun, just discard it
					logic = scan.next();
					int toStrip = logic.lastIndexOf(")");
					logic = logic.substring(0,toStrip);
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			}
			else if (s.contains("synth-fun")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // it's directly after synth-fun, just discard it
					functionName = scan.next();
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}

				funString = s.replace("synth-fun", "define-fun").trim();

				
				
				funString = funString.substring(0, funString.length() - 1) + " funToken;)";
				String funVariablesString = funString.substring(funString.indexOf(" " +functionName + " ") + functionName.length()+2, funString.lastIndexOf("funToken;"));
				funVariablesString = funVariablesString.substring(0, funVariablesString.lastIndexOf(")")).replace("(", "").replace(")", "");

				try(Scanner scan = new Scanner(funVariablesString)) {
					while(scan.hasNext()) {

						functionVariables.add(scan.next());
						functionVariableTypes.add(scan.next());
					}
				} catch(Exception e) {
					e.printStackTrace();
					throw e;
				}
				
				
				
			} else if (s.contains("declare-var")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); 
					variables.add(scan.next());
					variableTypes.add(scan.next().replace(")", ""));
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			} else if (s.contains("define-fun")) {
				definedFunctions.add(s);
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // function name directly after define-fun, for now we don't need to worry about
									// everything afterwards
					definedFunctionNames.add(scan.next());
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			} else if (s.contains("constraint")) {
				// //System.out.println(s);
				int idx = 12;
				constraints.add(s.substring(idx, s.length() - 1).trim());
			}
		}

		// //System.out.println(functionName);
		// //System.out.println(funString);
		String assertionString = "";
		if (constraints.size() == 1) {
			assertionString = constraints.get(0);
		} else {
			assertionString = "(and ";
			for (String con : constraints) {
				assertionString += con + " ";
			}
			assertionString += ")";
		}
		
		

		////System.out.println(assertionString);
		assertionString = Node.formatProgramStringForNode(assertionString);
		ArrayList<ArrayList<String>> invocations = findInvocations(assertionString,"("+ functionName + " ");
		
		
		////System.out.println("Hi");
		//String[] tmpVars = {"tmpvar1;", "tmpvar2;"};
		//String prog = "(- tmpvar1; tmpvar2;)";
		
		////System.out.println(transformSIProgramToMI(prog, variances, tmpVars));
		if (invocations == null) {
			throw new Exception("Unsupported Benchmark");
		}
		// //System.out.println(assertionString);
		String[] definedFunctionsArr;
		String[] definedFunctionNamesArr;
		if (definedFunctions.isEmpty()) {
			definedFunctionsArr = null;
			definedFunctionNamesArr = null;
		} else {
			definedFunctionsArr = definedFunctions.toArray(new String[definedFunctions.size()]);
			definedFunctionNamesArr = definedFunctionNames.toArray(new String[definedFunctionNames.size()]);

		}
	//	System.out.println(funString);
		funString = MIUtils.transformProgramFromInvocations(funString, functionVariables, variables);
		//System.out.println(funString);
		Benchmark b = new Benchmark(functionName, assertionString, funString, variables.toArray(new String[variables.size()]),
				definedFunctionsArr, definedFunctionNamesArr,logic, invocations);
		
		//b.setSynthesisVariableNames(variables.toArray(new String[variables.size()]));
		b.setVariableTypes(variableTypes.toArray(new String[variableTypes.size()]));
		b.setFunctionVariables(functionVariables.toArray(new String[functionVariables.size()]));
		b.setFunctionVariableTypes(functionVariableTypes.toArray(new String[functionVariableTypes.size()]));
		b.setConstants(constants);
		
		String[] extractionVariableNames = new String[b.getVariableNames().length];
		for (int i = 0; i < b.getVariableNames().length; i++) {
			extractionVariableNames[i] = "var" + (i+1) + ";";
		}
		
		b.setSynthesisVariableNames(extractionVariableNames);
		
		
		return b;
	}
	
	public int[] getConstants() {
		return constants;
	}

	public void setConstants(int[] constants) {
		this.constants = constants;
	}

	private static ArrayList<ArrayList<String>> findInvocations(String assertions, String targetFunction) {
		
		ArrayList<ArrayList<String>> invocations = new ArrayList<>();
		HashSet<String> invocationStrings = new HashSet<>();
		String principalString = "";

		String sub = assertions;
		while (true) {
			
			////System.out.println(sub);
			int idx = sub.indexOf(targetFunction);
			
			if (idx == -1) {
				break;
			}
			
			String funStringToExtract = Utils.extractNextFunction(sub.substring(idx));
			////System.out.println("Extracting: " + funStringToExtract);
			invocationStrings.add(funStringToExtract);
			principalString = funStringToExtract;
			idx += funStringToExtract.length();
			sub = sub.substring(idx);
		}
		
		ArrayList<String> principals = extractParameters(principalString.substring(targetFunction.length()));
		
		
		for (String s : invocationStrings) {
			ArrayList<String> checkParams = new ArrayList<>();
			checkParams.addAll(principals);
			ArrayList<String> params = extractParameters(s.substring(targetFunction.length()));
			
			for (String param : params) {
				if (checkParams.contains(param)) {
					checkParams.remove(param);
				} else {
					return null;
				}
			}
			
			invocations.add(params);
		}
		
		
		
		return invocations;
	}
	
	private static ArrayList<String> extractParameters(String varianceWithoutLeadingFunction) {
		
		
		ArrayList<String> params = new ArrayList<>();
		String sub = varianceWithoutLeadingFunction;
		String orig = sub;
		////System.out.println(sub);
		int idx = 0;
		while (true) {
			String nextParam = Utils.extractNextFunction(sub);
			
			params.add(nextParam);
			idx += nextParam.length() + 1;
			
			if (idx >= orig.length()) {
				break;
			}
			
			sub = orig.substring(idx);
			
		}
		
		return params;
		
	}
	
	private static int[] extractConstants(String benchmarkString) {
		HashSet<Integer> constants = new HashSet<>();
		String scanString = benchmarkString;
		constants.add(0);
		constants.add(1);
		constants.add(-1);
		
		scanString = scanString.replace("(", " ");
		scanString = scanString.replace(")", " ");
		
		
		try (Scanner scan = new Scanner(scanString)) {

			while (scan.hasNext()) {
				if (scan.hasNextInt()) {
					Integer c = scan.nextInt();
					constants.add(c);
					
				} else {
					scan.next();
				}

			}
		}
		
		int[] constantsArray = new int[constants.size()];
		int i = 0;
		for (Integer c : constants) {
			constantsArray[i] = c;
			i++;
		}
		
		
		return constantsArray;
		
	}
	public static void main(String[] args) throws Exception {
		String benchmarkFile = "src/main/resources/benchmarks/fg_array_sum_10_15.sl";
		//String benchmarkFile = "src/main/resources/benchmarks/fg_max4.sl";
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
		
		int[] constants = benchmark.getConstants();
		
		for (int c : constants) {
			//System.out.println(c);
		}
	}
	

}
