/**
 * Java version from the c++ code (https://github.com/FakePsyho/cpcontests/blob/master/various/cf_huawei_2023/main.cpp) 
 * developed by Psyho in the Huawei contest https://codeforces.com/contest/1885/problem/A
 */

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

public class Psyho {
	
	private static final double W = 192;
	
	
	private static int N;
	private static int K;
	private static int T;
	private static int R;
	private static int J;
	
	
	private static double[][][][] sinr;
	private static double[][][][] d;
	
	private static Frame[] frames;
	private static int[][] frame_id;
	
	private static List<List<Integer>> good_users;
	private static int[][] user_ok;
	private static List<Pair> frame_order;
	private static int cur_frame_order = 0;
	
	private static RNG rng = new RNG();
	private static State s;
	
	private static double[] l1_p;
    private static double[] l2_p;
    private static int[] la;
    private static int la_len = 0;
	
    private static long start = System.nanoTime();
    private static long time_passed = 0;
	
	private static class RNG {
		Random random = new SecureRandom();
			
		public int rand()
		{
			int r = random.nextInt();
			if(r < 0)
				r *= -1;
			return r;
		}
		
		public int next(int x)
		{
			return rand()%x;
		}
		
		public double next_double()
		{
			return Math.random();
		}
	}
	
	private static class Frame implements Comparable<Frame>{
		double tbs;
		int user;
		int start;
		int len;
		
		public Frame(double tbs, int user, int start, int len)
		{
			this.tbs = tbs;
			this.user = user;
			this.start = start;
			this.len = len;
		}

		@Override
		public int compareTo(Frame f) {
			return Double.compare(this.start, f.start);
		}
	}
	
	private static class Pair{
		double X;
		int Y;
		
		public Pair(double X, int Y)
		{
			this.X = X;
			this.Y = Y;
		}

		public double getX()
		{
			return X;
		}
		
		public double getY()
		{
			return Y;
		}
	}
	
	
	
	private static class State 
	{
		double[][][][] power = new double[T][K][R][N];
		double[][] power_usage = new double[T][K];
		double[][][] power_usage_single = new double[T][K][R];
		
		int[][][] total_r = new int[T][K][N];
		int[][] total_kr = new int[T][N];
		
		int[][][] power_1dlist_len = new int[T][K][R];
		int[][][][] power_1dlist = new int[T][K][R][N];
		int[][][][] power_1dlist_pos = new int[T][K][R][N];
		int[][] power_2dlist_len = new int[T][R];
		Pair[][][] power_2dlist = new Pair[T][R][N*K];
		int[][][][] power_2dlist_pos = new int[T][R][N][K];
		
		double[][] old_user_data = new double[T][N];
		double[][] user_data = new double[T][N];
		double[] frame_data = new double[J+1];
		
		double current_eval = 0;
		
		boolean[][] updated_group = new boolean[T][R];
		double[][][][] cur_data = new double[T][K][R][N]; 
		
		public State() {}	
		
		public void set_power(int t, int k, int r, int n, double v)
		{
			if(power[t][k][r][n] == v)
				return;
			
			power_usage[t][k] += v - power[t][k][r][n];
			power_usage_single[t][k][r] += v - power[t][k][r][n];
			if (v == 0) 
			{
	            total_r[t][k][n]--;
	            total_kr[t][n]--;
	            int p2d = power_2dlist_pos[t][r][n][k];
	            power_2dlist[t][r][p2d] = power_2dlist[t][r][--power_2dlist_len[t][r]];
	            power_2dlist_pos[t][r][(int)power_2dlist[t][r][p2d].X][power_2dlist[t][r][p2d].Y] = p2d;
	            power_2dlist_pos[t][r][n][k] = -1;
	            int p1d = power_1dlist_pos[t][k][r][n];
	            power_1dlist[t][k][r][p1d] = power_1dlist[t][k][r][--power_1dlist_len[t][k][r]];
	            power_1dlist_pos[t][k][r][power_1dlist[t][k][r][p1d]] = p1d;
	            power_1dlist_pos[t][k][r][n] = -1;
	        } 
			else if (power[t][k][r][n] == 0) 
			{
	            total_r[t][k][n]++;
	            total_kr[t][n]++;
	            power_2dlist_pos[t][r][n][k] = power_2dlist_len[t][r];
	            power_2dlist[t][r][power_2dlist_len[t][r]++] = new Pair(n, k);
	            power_1dlist_pos[t][k][r][n] = power_1dlist_len[t][k][r];
	            power_1dlist[t][k][r][power_1dlist_len[t][k][r]++] = n;
	        }
	        updated_group[t][r] = true;
	        power[t][k][r][n] = v;
		}
		
		public double eval_frame(int j) 
		{
	        return frame_data[j] >= frames[j].tbs ? 1.0 : 0.10 * Math.pow(frame_data[j] / frames[j].tbs, 3.50);        
	    }
		
		public void calc_user_data(int t) 
		{
	        for (int n : good_users.get(t)) 
	        {
	            current_eval -= eval_frame(frame_id[t][n]);
	            frame_data[frame_id[t][n]] = Math.max(frame_data[frame_id[t][n]] - user_data[t][n], 0.0);
	            current_eval += eval_frame(frame_id[t][n]);
	            old_user_data[t][n] = user_data[t][n];
	            user_data[t][n] = 0;
	        }

	        for (int n0 : good_users.get(t))
	        {
	        	if (total_kr[t][n0] > 0)
	        	{
	        		for(int k0 = 0; k0 < K; k0++) 
	        		{
			            if (total_r[t][k0][n0] == 0) 
			            	continue;
		
			            double total_s = 1;
			            
			            for(int r = 0; r < R; r++)
			            {
			            	if (power[t][k0][r][n0] > 0) 
			            	{
				                if (updated_group[t][r]) 
				                {
				                    double q = 1.0;
				                    double p = sinr[t][k0][r][n0] * power[t][k0][r][n0];
				                    for(int i = 0; i < power_2dlist_len[t][r]; i++)
				                    {
				                        var n = (int)(power_2dlist[t][r][i].X);
				                        var k = power_2dlist[t][r][i].Y;
				                        if (k == k0) {
				                            p /= d[k0][r][n0][n];
				                        } else {
				                            q += (n0 != n ? 1 : 0) * sinr[t][k][r][n0] * power[t][k][r][n] * d[k][r][n0][n];
				                        }
				                    }
			
				                    cur_data[t][k0][r][n0] = p / q;
				                }
				                total_s *= cur_data[t][k0][r][n0];
			            	}
			            }
			            total_s = Math.pow(total_s, 1.0 / total_r[t][k0][n0]);
		
			            user_data[t][n0] += total_r[t][k0][n0] * log2(1.0 + total_s);
	        		}
	        	}
	        }

	        for(int r = 0; r < R; r++)
	        	updated_group[t][r] = false;

	        for (int n : good_users.get(t)) {
	            current_eval -= eval_frame(frame_id[t][n]);
	            frame_data[frame_id[t][n]] += user_data[t][n];
	            current_eval += eval_frame(frame_id[t][n]);
	        }
	    }
		
		
		public void restore_user_data(int t) 
		{
	        for (int n : good_users.get(t))
	        {
	        	if (user_data[t][n] != old_user_data[t][n]) 
	        	{
	        		frame_data[frame_id[t][n]] = Math.max(frame_data[frame_id[t][n]] + old_user_data[t][n] - user_data[t][n], 0.0);
	        		user_data[t][n] = old_user_data[t][n];
	        	}
	        }
	    }
		
		public double eval() 
		{
	        return current_eval;
	    }

	    public double recalc_user_data() {
	    	for(int t = 0; t < T; t++)
	    		calc_user_data(t);
	    	return eval();
	    }

	    public double calc_score() {
	        int total_frames = 0;
	        
	        for(int j = 0; j < J; j++)
	        	total_frames += (frame_data[j] >= frames[j].tbs ? 1 : 0);
	        return total_frames;
	    }
 	}
	
	private static void add_frame()
	{
		int f = frame_order.get(cur_frame_order++).Y;
		for(int i = frames[f].start; i < frames[f].start + frames[f].len; i++)
		{
			//user_ok.get(i).set(frames[f].user, 1);
			user_ok[i][frames[f].user] = 1;
	        good_users.get(i).add(frames[f].user);
	        frame_id[i][frames[f].user] = f;
		}
	}
	
	private static double log2(double v1)
	{
		return Math.log(v1) / Math.log(2);
	}


	
	public static void main(String[] args) throws Exception{
		BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(System.in));
		
		N = Integer.parseInt(bufferedReader.readLine());
		K = Integer.parseInt(bufferedReader.readLine());
		T = Integer.parseInt(bufferedReader.readLine());
		R = Integer.parseInt(bufferedReader.readLine());
		
		sinr = new double[T][K][R][N];
		d = new double[K][R][N][N];
		
		frame_id = new int[T][N];
		l1_p = new double[N];
		l2_p = new double[N];
		la = new int[N];
		
		
		for(int t = 0; t < T; t++)
		{
			for(int k = 0; k < K; k++)
			{
				for(int r = 0; r < R; r++)
				{
					String[] sinrLine = bufferedReader.readLine().split(" ");
					for(int n = 0; n < N; n++)
					{
						sinr[t][k][r][n] = Double.parseDouble(sinrLine[n]);
					}
				}
			}
		}
		
		double d_sum = 0;
		for(int k = 0; k < K; k++)
		{
			for(int r = 0; r < R; r++)
			{
				for(int m = 0; m < N; m++)
				{
					String[] ifLine = bufferedReader.readLine().split(" ");
					for(int n = 0; n < N; n++)
					{
						double v = -Double.parseDouble(ifLine[n]);
						d_sum += v;
						d[k][r][m][n] = Math.exp(v);
					}
				}
			}
		}
		double d_avg = d_sum / (K * R * N * N);
		
		
		
		J = Integer.parseInt(bufferedReader.readLine());
		frames = new Frame[J];
		for(int j = 0; j < J; j++)
		{
			String[] fLine = bufferedReader.readLine().split(" ");
			double tbs = Double.parseDouble(fLine[1])*(1+1e-6) / W;
			int user = Integer.parseInt(fLine[2]);
			int start = Integer.parseInt(fLine[3]);
			int len = Integer.parseInt(fLine[4]);
			
			frames[j] = new Frame(tbs, user, start, len);
		}
		Arrays.sort(frames);
		
		for(int k = 0; k < K; k++)
		{
			for(int r = 0; r < R; r++)
			{
				for(int n = 0; n < N; n++)
				{
					d[k][r][n][n] = 1;
				}
			}
		}
		
		s = new State();
		
		user_ok = new int[T][N];
		good_users = new ArrayList<>();
		frame_order = new ArrayList<Pair>();
		for(int t = 0; t < T; t++)
		{
			//user_ok.add(new ArrayList<>());
			good_users.add(new ArrayList<>());
			for(int n = 0; n < N; n++)
			{
				//user_ok.get(t).add(0);
				frame_id[t][n] = J;
			}
		}
		
		boolean[] obtainable = new boolean[J];
		for(int j = 0; j < J; j++)
		{
			double data = 0;
			for(int t = frames[j].start; t < frames[j].start + frames[j].len; t++)
			{
				for(int k = 0; k < K; k++)
				{
					double best_sinr = 0;
					for(int r = 0; r < R; r++)
						best_sinr = Math.max(best_sinr, sinr[t][k][r][frames[j].user]);
					double best_data = 0;
	                for(int r = 1; r < R+1; r++)
	                {
	                	double v = W * r * log2(1 + best_sinr * R / r);
	                    if (v > best_data) {
	                        best_data = v;
	                    }
	                }
	                data += best_data;
	                if (data >= frames[j].tbs) 
	                	break;
				}
				if (data >= frames[j].tbs) 
					break;
			}
			obtainable[j] = data >= frames[j].tbs;
		}
		
		for(int j = 0; j < J; j++)
			if (obtainable[j]) 
				frame_order.add(new Pair((int)frames[j].tbs, j));
		
		Comparator<Pair> compare = Comparator.comparing(Pair::getX).thenComparing(Pair::getY);
		frame_order = frame_order.subList(0, frame_order.size()).stream().sorted(compare).collect(Collectors.toList());
		for(int i = 0; i < frame_order.size(); i++)
			add_frame();
		for(int t = 0; t < T; t++)
			Collections.sort(good_users.get(t));
		
		int[] used_k = new int[K];
		int[] used_n = new int[N];
		int[] k_rows = new int[K];
		
		List<List<Integer>> used_kn = new ArrayList<>();
		for(int k = 0; k < K; k++)
		{
			used_kn.add(new ArrayList<>());
			for(int n = 0; n < N; n++)
				used_kn.get(k).add(0);
		}
		
		List<List<Integer>> rlist = new ArrayList<>();
		for(int r = 0; r < R; r++)
			rlist.add(new ArrayList<>());
		
		int[] rpos = new int[R];
		for(int r = 0; r < R; r++)
			rpos[r] = -1;
		
		
		double[][][] dmul = new double[R][N][N];
		for(int k = 0; k < K; k++)
		{
			for(int r = 0; r < R; r++)
			{
				for(int n = 0; n < N; n++)
				{
					for(int n2 = 0; n2 < N; n2++)
					{
						if(k == 0)
							dmul[r][n][n2] = 1;
						dmul[r][n][n2] *= d[k][r][n][n2];
					}
				}
			}
		}
		
		
		for(int t = 0; t < T; t++)
		{
			if (d_avg > 0.5) 
				break;
	        if (good_users.get(t).size() == 0) 
	        	continue;
	        
	        double[][] rpos_value = new double[R][K];
	        
	        for(int r = 0; r < R; r++)
	        {
	        	for(int k = 0; k < K; k++)
	        	{
	        		double total_value = 0;

	                double avg_sinr = 1.0;
	                for (int n : good_users.get(t)) 
	                	avg_sinr *= sinr[t][k][r][n];
	                avg_sinr = Math.pow(avg_sinr, 1.0 / good_users.get(t).size());

	                for (int n : good_users.get(t)) {
	                    double cur_d = 1.0;
	                    for (int n2 : good_users.get(t)) 
	                    	if (n != n2) 
	                    		cur_d *= d[k][r][n][n2];
	                    double cur_dd = 1.0;
	                    if (K > R) for (int n2 : good_users.get(t)) 
	                    	if (n != n2) 
	                    		cur_dd *= dmul[r][n][n2];
	                    total_value += Math.log(1 + avg_sinr / Math.pow(cur_d, 1.0) / Math.pow(cur_dd, 0.1));
	                }
	                rpos_value[r][k] = total_value;
	        	}
	        }
	        
	        for(int r = 0; r < R; r++)
	        	rpos[r] = -1;
	        
	        for(int k = 0; k < K; k++)
	        	k_rows[k] = 0;
	        
	        for(int rstep = 0; rstep < R; rstep++)
	        {
	        	double bv = -1e9;
	            int br = -1;
	            int bk = -1;
	            for(int r = 0; r < R; r++)
	            {
	            	if (rpos[r] == -1)
	            	{
	            		for(int k = 0; k < K; k++)
	            		{
	            			double av = rpos_value[r][k] - k_rows[k] * 1000;
	                        if (av > bv) {
	                            bv = av;
	                            br = r;
	                            bk = k;
	                        }
	            		}
	            	}
	            }
	            rpos[br] = bk;
	            k_rows[bk]++;
	        }
	        
	        for(int step = 0; step < 500; step++)
	        {
	        	if (rng.next(2) > 0) {
	                int r1 = rng.next(R);
	                int r2 = rng.next(R);
	                if (r1 == r2) 
	                	continue;
	                double v1 = rpos_value[r1][rpos[r1]] * rpos_value[r2][rpos[r2]];
	                double v2 = rpos_value[r1][rpos[r2]] * rpos_value[r2][rpos[r1]];
	                if (v2 >= v1)
	                {
	                	int aux = rpos[r1];
	                	rpos[r1] = rpos[r2];
	                	rpos[r2] = aux;
	                }
	            } else {
	                int r1 = rng.next(R);
	                int nk = rng.next(K);
	                if (k_rows[rpos[r1]] <= k_rows[nk]) 
	                	continue;
	                double v1 = rpos_value[r1][rpos[r1]];
	                double v2 = rpos_value[r1][nk];
	                if (v2 >= v1) 
	                {
	                	rpos[r1] = nk;
	                	k_rows[nk]++; 
	                	k_rows[rpos[r1]]--;
	                }
	            }
	        }
	        
	        for(int r = 0; r < R; r++)
	        	rlist.get(r).removeAll(rlist.get(r));
	        
	        for(int k = 0; k < K; k++)
	        	for(int n = 0; n < N; n++)
	        		used_kn.get(k).set(n, 0);
	        
	        List<Pair> user_list = new ArrayList<>();
	        for(int n: good_users.get(t))
	        	user_list.add(new Pair(frames[frame_id[t][n]].tbs, n));
	        
	        user_list = user_list.stream().sorted(compare).collect(Collectors.toList());
	        
	        List<Pair> build_order = new ArrayList<>();
	        for(int rep = 0; rep < Math.max(1, Math.min(R, Math.min((int)R, 4000 / (int)good_users.get(t).size() / (int)good_users.get(t).size()))); rep++)
	        {
	        	for(var p: user_list)
	        	{
	        		int n = p.Y;
	                double bv = -1e9;
	                int bk = -1;
	                int br = -1;
	                for(int r = 0; r < R; r++)
	                {
	                	if(rpos[r] == -1)
	                		continue;
	                	int k = rpos[r];
	                    double badd = 1.0;
	                    for (int x : rlist.get(r)) 
	                    	badd /= d[k][r][n][x]; 
	                    for(int r2 = 0; r2 < R; r2++)
	                    {
	                    	if (r2 != r && rpos[r2] == k) 
	                    	{
	                    		for (int x : rlist.get(r2)) 
	                    			badd /= d[k][r][n][x];
	                    	}
	                    }
	                    double av = Math.log(1 + sinr[t][k][r][n] * badd) + rng.next_double() - rlist.get(r).size() * 10 - used_k[k] * 100 + used_kn.get(k).get(n) * 1000;
	                    for (int x : rlist.get(r)) 
	                    	av -= 1e6 * (n == x ? 1 : 0);
	                    if (av > bv) {
	                        bv = av;
	                        bk = k;
	                        br = r;
	                    }
	                }
	                used_k[bk]++;
	                used_n[n]++;
	                used_kn.get(bk).set(n, used_kn.get(bk).get(n)+1);
	                rpos[br] = bk;
	                build_order.add(new Pair(br, rlist.get(br).size()));
	                rlist.get(br).add(n);
	        	}
	        }
	        
	        for(int r = 0; r < R; r++)
	        {
	        	if (rpos[r] != -1)
	        	{
	        		int k = rpos[r];
	                double available_power = 4.0;
	                int total_k = 0; 
	                for(int r2 = 0; r2 < R; r2++)
	                	total_k += (rpos[r] == rpos[r2] ? 1 : 0);
	                available_power = Math.min(available_power, 1.0 * R / total_k);
	                for (int n : rlist.get(r)) 
	                {
	                    if (s.frame_data[frame_id[t][n]] >= frames[frame_id[t][n]].tbs) 
	                    	continue;
	                    s.set_power(t, k, r, n, available_power / rlist.get(r).size());
	                    s.calc_user_data(t);
	                }
	        	}
	        }
		}
		
		double bv = s.recalc_user_data();
	    double printed_bv = bv;
	    double last_print = 0.0;
		
	    int step = 0;
	    final double t0 = (frames[0].len == 1 ? 0.004 : 1e-5);
	    final double tn = (frames[0].len == 1 ? 1e-6 : 1e-9);
	    double temp = t0;
	    
	    double[][] move_weights = new double[][] {{5.0, 1.8, 0.5, 0.4, 0.4, 0.25}, {5.0, 1.8, 0.5, 0.4, 0.4, 0.25}};
	    
	    for(int ph = 0; ph < 2; ph++)
	    {
	    	double wsum = 0;
	    	for(double w: move_weights[ph])
	    		wsum += w;
	    	for(int id = 0; id < 6; id++)
	    	{
	    		move_weights[ph][id] = move_weights[ph][id]/wsum;
	    	}
	    	for(int i = 1; i < 6; i++)
	    		move_weights[ph][i] += move_weights[ph][i-1];
	    	move_weights[ph][5] = 1.0;
	    }
	    
	    int type = 0;
	    int attempt = 0;

	    List<Integer> times_left = new ArrayList<>();
	    int[] frames_left = new int[T];
	    for(int t = 0; t < T; t++)
	    {
	    	for(int n: good_users.get(t))
	    	{
	    		if(s.frame_data[frame_id[t][n]] < frames[frame_id[t][n]].tbs)
	    			frames_left[t]++;
	    	}
	    	if(frames_left[t] > 0)
	    		times_left.add(t);
	    }
	    
	    int phase = 0;
	    
	    long extraTime = 1655000000L;
	    
	    long end = start + extraTime;

	    while (System.nanoTime() < end)
	    {
	    	int t;
	    	if (frames[0].len == 1 || rng.next_double() < 0.70) {
	            if (times_left.size() == 0) 
	            	break;
	            t = times_left.get(rng.next(times_left.size()));
	        } else {
	            t = rng.next(T);
	            if (good_users.get(t).size() == 0) 
	            	continue;
	        }
	    	
	    	int k = rng.next(K);

	        int t2=0, k2=0, r=0, r2=0, cur_n=0, new_n=0, cur_n2=0, new_n2=0;
	        double cur_power=0, cur_power2=0, new_power=0, new_power2=0;

	        if (attempt == 0 || attempt >= 10) {
	            double rtype = rng.next_double();
	            type = 0; 
	            while (rtype > move_weights[phase][type]) 
	            	type++;
	        }
	        attempt++;

	        final double RR = 0.55;
	        final double T0_ZERO = d_avg > 0.5 ? 0.5 : 0.30;
	        
	        if (type == 0) {
	            r = rng.next(R);

	            if (rng.next_double() < 0.4) 
	            {
	                cur_n = s.power_1dlist_len[t][k][r] > 0 ? s.power_1dlist[t][k][r][rng.next(s.power_1dlist_len[t][k][r])] : -1;
	                if (cur_n == -1) 
	                	continue;
	            } else {
	                cur_n = good_users.get(t).get(rng.next(good_users.get(t).size()));
	            }

	            
	            cur_power = s.power[t][k][r][cur_n];
	            if (cur_power == 0 && s.frame_data[frame_id[t][cur_n]] > frames[frame_id[t][cur_n]].tbs && rng.next_double() < 0.85) 
	            	continue;
	            double max_power = Math.max(0.0, Math.min(R - s.power_usage[t][k] + cur_power, 4.0 - s.power_usage_single[t][k][r] + cur_power));
	            new_power = rng.next_double() < T0_ZERO ? 0.0 : Math.pow(rng.next_double(), 0.5) * max_power;
	            

	            if (cur_power == new_power) 
	            	continue;

	        } 
	        else if (type == 1) 
	        {
	            r = rng.next(R);
	            if (s.power_1dlist_len[t][k][r] == 0) 
	            	continue;

	            cur_n = s.power_1dlist[t][k][r][rng.next(s.power_1dlist_len[t][k][r])];
	            cur_n2 = rng.next_double() < 0.2 ? good_users.get(t).get(rng.next(good_users.get(t).size())) : s.power_1dlist[t][k][r][rng.next(s.power_1dlist_len[t][k][r])];
	            if (cur_n == cur_n2) 
	            	continue;

	            cur_power = s.power[t][k][r][cur_n];
	            cur_power2 = s.power[t][k][r][cur_n2];
	            double power_diff = frames[0].len > 1 && rng.next_double() < 0.8 || rng.next_double() < RR ? cur_power : rng.next_double() * cur_power;
	            if (cur_power == 0 && s.frame_data[frame_id[t][cur_n2]] > frames[frame_id[t][cur_n2]].tbs && rng.next_double() < 0.50) 
	            	continue;

	            new_power = cur_power - power_diff;
	            new_power2 = cur_power2 + power_diff;
	            new_power2 = Math.max(new_power2, 0.0);
	        } 
	        else if (type == 2) 
	        {
	            r = rng.next(R);
	            r2 = rng.next(R);
	            if (r == r2) 
	            	continue;
	            if (s.power_1dlist_len[t][k][r] == 0) 
	            	continue;

	            cur_n = s.power_1dlist[t][k][r][rng.next(s.power_1dlist_len[t][k][r])];
	            cur_power = s.power[t][k][r][cur_n];
	            cur_power2 = s.power[t][k][r2][cur_n];

	            if (cur_power == 0 && s.frame_data[frame_id[t][cur_n]] > frames[frame_id[t][cur_n]].tbs && rng.next_double() < 0.50) 
	            	continue;
	            double power_diff = rng.next_double() < RR ? cur_power : rng.next_double() * cur_power;

	            new_power = cur_power - power_diff;
	            new_power2 = cur_power2 + power_diff;
	            new_power2 = Math.min(new_power2, 4.0 - s.power_usage_single[t][k][r2] + cur_power2);
	            new_power2 = Math.max(new_power2, 0.0);

	        } 
	        else if (type == 3) {
	            r = rng.next(R);
	            k2 = rng.next(K);
	            if (k == k2) 
	            	continue;
	            if (s.power_1dlist_len[t][k][r] == 0) 
	            	continue;

	            cur_n = s.power_1dlist[t][k][r][rng.next(s.power_1dlist_len[t][k][r])];
	            cur_power = s.power[t][k][r][cur_n];
	            cur_power2 = s.power[t][k2][r][cur_n];

	            if (cur_power == 0 && s.frame_data[frame_id[t][cur_n]] > frames[frame_id[t][cur_n]].tbs && rng.next_double() < 0.50) 
	            	continue;
	            double power_diff = rng.next_double() < RR ? cur_power : rng.next_double() * cur_power;

	            new_power = cur_power - power_diff;
	            new_power2 = cur_power2 + power_diff;
	            new_power2 = Math.min(new_power2, 4.0 - s.power_usage_single[t][k2][r] + cur_power2);
	            new_power2 = Math.min(new_power2, R - s.power_usage[t][k2] + cur_power2);
	            new_power2 = Math.max(new_power2, 0.0);
	        } 
	        else if (type == 4) 
	        {
	            r = rng.next(R);
	            k2 = rng.next(K);
	            if (k == k2) 
	            	continue;
	            if (s.power_usage[t][k] - s.power_usage_single[t][k][r] + s.power_usage_single[t][k2][r] > R) 
	            	continue;
	            if (s.power_usage[t][k2] - s.power_usage_single[t][k2][r] + s.power_usage_single[t][k][r] > R) 
	            	continue;
	        } 
	        else if (type == 5) 
	        {
	            r2 = rng.next(R);
	            if (r2 == r) continue;
	        }
	        attempt = 0;
	        
	        step++;

	        if ((step & 31) == 0) 
	        {
	            double PHASE0_LENGTH = frames[0].len == 1 ? 0.2 : 0.0;
	            time_passed = (System.nanoTime() - start) / end;
	            phase = time_passed < PHASE0_LENGTH ? 0 : 1;
	            temp = t0 * Math.pow(tn / t0, Math.pow(phase == 0 ? 1.0 : (time_passed - PHASE0_LENGTH), 1.50));
	            if (time_passed > 1.0) 
	            	break;
	        }

	        if (type == 0) 
	        {
	            s.set_power(t, k, r, cur_n, new_power);
	        } 
	        else if (type == 1) 
	        {
	            s.set_power(t, k, r, cur_n, new_power);
	            s.set_power(t, k, r, cur_n2, new_power2);
	        } 
	        else if (type == 2) 
	        {
	            s.set_power(t, k, r, cur_n, new_power);
	            s.set_power(t, k, r2, cur_n, new_power2);
	        } 
	        else if (type == 3) 
	        {
	            s.set_power(t, k, r, cur_n, new_power);
	            s.set_power(t, k2, r, cur_n, new_power2);
	        } 
	        else if (type == 4) 
	        {
	            la_len = 0;
	            for(int n = 0; n < N; n++)
	            {
	            	if (s.power[t][k][r][n] > 0 || s.power[t][k2][r][n] > 0) 
	            	{
		                la[la_len++] = n;
		                l1_p[n] = s.power[t][k][r][n];
		                l2_p[n] = s.power[t][k2][r][n];
		                s.set_power(t, k, r, n, l2_p[n]);
		                s.set_power(t, k2, r, n, l1_p[n]);
		            }
	            }
	        } 
	        else if (type == 5) 
	        {
	        	for(int kv = 0; kv < K; kv++)
	        	{
	        		if (s.power_usage_single[t][kv][r] > 0 || s.power_usage_single[t][kv][r2] > 0)
	        		{
	        			for (int n : good_users.get(t)) 
	        			{
	        				if (s.power[t][kv][r][n] > 0 || s.power[t][kv][r2][n] > 0) 
	        				{
				                double p1 = s.power[t][kv][r][n];
				                double p2 = s.power[t][kv][r2][n];
				                s.set_power(t, kv, r, n, p2);
				                s.set_power(t, kv, r2, n, p1);
	        				}
	        			}
	        		}
	            }
	        }
	        s.calc_user_data(t);
	        
	        double av = s.eval();

	        if (av >= bv || rng.next_double() < Math.exp((av - bv) / temp)) 
	        {
                frames_left[t] = 0;
                for (int n : good_users.get(t)) 
                {
                	if (s.frame_data[frame_id[t][n]] < frames[frame_id[t][n]].tbs) 
                		frames_left[t]++;
                }
                if (frames_left[t] == 0) {
                	for(int i = 0; i < times_left.size(); i++)
                	{
                		if (times_left.get(i) == t)
                		{
                			times_left.set(i, times_left.get(times_left.size()-1));
                			times_left.remove(times_left.size()-1);
	                        break;
                		}
                	}
                }

	            if ((int)av > (int)printed_bv && time_passed > last_print + 0.05) 
	            {
	                printed_bv = av;
	                last_print = time_passed;
	            }
	            bv = av;
	        } 
	        else 
	        {
	            if (type == 0) 
	            {
	                s.set_power(t, k, r, cur_n, cur_power);
	            } 
	            else if (type == 1) 
	            {
	                s.set_power(t, k, r, cur_n, cur_power);
	                s.set_power(t, k, r, cur_n2, cur_power2);
	            } 
	            else if (type == 2) 
	            {
	                s.set_power(t, k, r, cur_n, cur_power);
	                s.set_power(t, k, r2, cur_n, cur_power2);
	            } 
	            else if (type == 3) 
	            {
	                s.set_power(t, k, r, cur_n, cur_power);
	                s.set_power(t, k2, r, cur_n, cur_power2);
	            } 
	            else if (type == 4) 
	            {
	            	for(int i = 0; i < la_len; i++)
	            	{
	                    int n = la[i];
	                    s.set_power(t, k, r, n, l1_p[n]);
	                    s.set_power(t, k2, r, n, l2_p[n]);
	                }
	            } 
	            else if (type == 5) 
	            {
	            	for(int kv = 0; kv < K; kv++)
	            	{
	            		if (s.power_usage_single[t][kv][r] > 0 || s.power_usage_single[t][kv][r2] > 0)
	            		{
	            			for (int n : good_users.get(t)) 
	            			{
		            			if (s.power[t][kv][r][n] > 0 || s.power[t][kv][r2][n] > 0) 
		            			{
				                    double p1 = s.power[t][kv][r][n];
				                    double p2 = s.power[t][kv][r2][n];
				                    s.set_power(t, kv, r, n, p2);
				                    s.set_power(t, kv, r2, n, p1);
		            			}
	            			}
	            		}
	                }
	            }
	            s.current_eval = bv;
	            s.restore_user_data(t);
	        }
	    }
	    
	    StringBuilder string_builder = new StringBuilder();
	    for(int t = 0; t < T; t++)
	    {
	    	for(int k = 0; k < K; k++)
	    	{
	            double sumk = 0;
	            for(int r = 0; r < R; r++)
	            {
	                double sumr = 0;
	                for(int n = 0; n < N; n++)
	                {
	                	double v = Math.max(0.0, Math.min(4.0 - sumr, Math.min(R - sumk, s.power[t][k][r][n])));
	                    sumr += v;
	                    sumk += v;
	                    if (v < 1e-9)
	                    	string_builder.append("0 ");
	                    else
	                    	string_builder.append(v + " ");
	                }
	                string_builder.append("\n");
	            }
	    	}
	    }
	    
	    System.out.println(string_builder);
	    
	    //System.out.println(s.calc_score());
		
		bufferedReader.close();
	}

}
