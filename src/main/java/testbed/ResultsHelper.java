package testbed;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Scanner;

public class ResultsHelper {

	public static void main(String[] args) throws IOException {
		
		
		
		//Path filePath = Path.of("C:\\Users\\twels\\Documents\\Thesis\\results\\CBPSResults");

		//String content = Files.readString(fileName);
		
		String directory = "C:\\Users\\twels\\Documents\\Thesis\\results\\CBPSResults";


		ArrayList<ArrayList<Integer>> times = new ArrayList<>();
		

		//ArrayList<String> benchmarkNames = new ArrayList<>();
		File[] files = new File(directory).listFiles();
		
		int numBenchmarks = 75;
		for (int i = 0; i < numBenchmarks; i++) {
			times.add(new ArrayList<Integer>());
		}
		
		ArrayList<String> names = new ArrayList<>();
		
		boolean buildFileNames = true;
		//int i = 0;
		for (File file : files) {
			//System.out.println(Files.readString(file.toPath()));
			List<String> rows = Files.readAllLines(file.toPath());
			rows.remove(0);
			for (int j = 0; j < rows.size(); j++) {
				Scanner s = new Scanner(rows.get(j));
				s.useDelimiter(",");
				
				if (buildFileNames) {
				names.add(s.next());
				} else {
					s.next();
				}
				 

				s.next();
				times.get(j).add(s.nextInt());
				
				//System.out.println(s.nextInt());
			}
			
			buildFileNames = false;
		}
		
		ArrayList<Integer> maxes = new ArrayList<>();
		ArrayList<Integer> medians = new ArrayList<>();
		for (int i = 0; i < times.size(); i++) {
			maxes.add(Collections.max(times.get(i)));
			Collections.sort(times.get(i));
		
			int median = (times.get(i).get(4) + times.get(i).get(5)) /2;
			medians.add(median);
			
		}
		System.out.println(maxes.size());
		System.out.println(names.size());
		String resultsAsCSV = "benchmark,max,median\n";
		for (int i = 0; i < maxes.size(); i++) {
			System.out.println(names.get(i) + "," + maxes.get(i) + "," + medians.get(i));
			resultsAsCSV += names.get(i) + "," + maxes.get(i) + "," + medians.get(i) + "\n";
		}
		
		BufferedWriter writer = new BufferedWriter(new FileWriter("CBPSresults.csv"));
		writer.write(resultsAsCSV);

		writer.close();
		
		
		
	}
	
	
	
}
