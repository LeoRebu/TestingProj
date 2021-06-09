import java.util.ArrayList; 

public class Colonia {

	private String name;
	private int yobQueen;
	private int qualityQueen;
	private int totHoney;
	private ArrayList<Report> reportList;
	
	public Colonia() {
		name="";
		yobQueen=2015;
		qualityQueen=1;
		totHoney=0;
		reportList = new ArrayList<Report>();
	}
	
	public Colonia(String n, int yq, int qq, int th, ArrayList<Report> rl) {
		name=n;
		yobQueen=yq;
		qualityQueen=qq;
		totHoney=th;
		reportList = rl;
	}
	
	public void setName(String n) {
		name = n;		
	}
	public void setYobQueen(int yq) {
		yobQueen = yq;		
	}
	public void setQualQueen(int qq) {
		qualityQueen = qq;		
	}
	public void increaseTotalHoney(int th) {
		totHoney += th;		
	}
	public void addReport(Report report) {
		reportList.add(report);		
	}
	
	public String getName() {
		return name;
	}
	public int getYobQueen() {
		return yobQueen;
	}
	public int getQualQueen() {
		return qualityQueen;
	}
	public int getTotalHoney() {
		return totHoney;
	}
	public ArrayList<Report> getReports() {
		return reportList;
	}
}
