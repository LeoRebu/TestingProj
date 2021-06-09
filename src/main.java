import java.util.ArrayList;
import java.util.Scanner;
import java.io.File;
import java.io.FileNotFoundException;

public class main {
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		ArrayList<Colonia> listaColonie = new ArrayList<Colonia>();
		String nomeFile = "colonie.txt";
		//ArrayList<String> 
		importFile(nomeFile,listaColonie);

		 System.out.println(listaColonie.get(0).getName());
	}
	
	public static void importFile (String nomeFile, ArrayList<Colonia> lc) {
		try {
			File myFile = new File(nomeFile);
			Scanner myReader = new Scanner(myFile);
			while (myReader.hasNextLine()) {
			    String colony = myReader.nextLine();
			    String delim = "[|]+";
			    String[] colonyData = colony.split(delim);
			    Colonia c = new Colonia();
			    c.setName(colonyData[0]);
			    c.setYobQueen(Integer.parseInt(colonyData[1]));
			    c.setQualQueen(Integer.parseInt(colonyData[2]));
			    c.increaseTotalHoney(Integer.parseInt(colonyData[3]));
			    
			    lc.add(c);
		    }
		    myReader.close();
		 } catch (FileNotFoundException e) {
			 System.out.println("An error occurred.");
			 e.printStackTrace();
		 }
	}

}
