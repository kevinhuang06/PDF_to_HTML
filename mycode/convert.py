#coding=utf-8
from simplePDF2html import *
import os
import copy
import glob

def get_HTML_fname(pdf_name):
	parts = pdf_name.split('.')
	assert len(parts) == 2, "Could Only handle path with one '.'"
	return reduce(lambda x, y: x + y, parts[:-1] + ['_content.html'])
 
def get_PDF_fnames(directory):
	fnames = os.listdir(directory)
	PDF_names = []
	for name in fnames:
		if name.split('.')[-1] in ['PDF', 'pdf']:
			PDF_names.append(directory + name)
	return PDF_names

fname_list = []
# get_PDF_fnames('data/')

# fname_list = ['data/simple1.PDF']
# fname_list = ['data/outline_example_1.pdf']

# fname_list = ['data/table_example_1.pdf', 'data/table_example_2.pdf', 'data/table_example_3.pdf', 'data/table_example_4.pdf', 'data/table_example_5.pdf', 'data/table_example_6.pdf', 'data/table_example_7.pdf', 'data/table_example_8.pdf']
#fname_list = ['data/2017-03-30-1203224890.PDF']
#fname_list = ['data/2016-01-19-1201924055.PDF']
#fname_list = ['data2/2016-04-25-1202237114.PDF'] #9 # 5 # 11 #12 # 14
#'data2/bad_case/2014-12-29-64666524.PDF'
#fname_list = ['data2/bad_case/2016-10-12-1202754801.PDF']#'data2/2016-08-11-1202559993.PDF'] # table testcase
#fname_list = ['pdf/good/2017-04-10-1203280460.PDF']
#fname_list = ['data2/2016-04-25-1202255836.PDF']
#fname_list = ['pdf/good/2016-08-26-1202648670.PDF']
#fname_list=['pdf/bad_html/2013-04-22-62408598.PDF']
#fname_list = ['data/table_example_18.pdf']
# fname_list = ['data/simple1.PDF', 'data/simple2.PDF', 'data/simple3.PDF']
#fname_list = ['pdf/table/table_example_19.pdf']

#fname_list = ['pdf/table/bt_table_11_2017-04-28_1203411656.PDF']
#fname_list = ['pdf/table/bt_table_6-16_2017-04-28_1203411656.PDF']
fname_list = ['data/table_example_15.PDF']
#fname_list = ['pdf/table/table_65_2016-08-26-1202648670.PDF']
#fname_list = ['data2/2016-08-30-1202642653.PDF']
#fname_list=['pdf/table/table_90_2016-04-25-1202255836.PDF']
# 失败的表格
#fname_list = ['pdf/table/page_42_2016-07-29-1202527287.PDF']
#fname_list = ['pdf/table/page_140_2016-04-28-1202256878.PDF']
#fname_list = ['data2/2016-07-29-1202527287.PDF']
# fname_list = get_PDF_fnames('data/')

'data2/2016-08-30-1202642653.PDF'
'2016-04-28-1202256878.PDF'
'data2/2016-07-29-1202527287.PDF'
# empty_colspan[representer_j] += 1
'data2/2016-10-12-1202751015.PDF'
#for file_name in glob.glob(r"data/*.pdf"):
#for file_name in glob.glob(r"data2/*.PDF"):
#	fname_list.append(file_name)
# #print fname_list

COUNT = True
if COUNT:
	cnt_total = 0
	cnt_success = 0
	unsuccess = []
bias_param_list = [[2, 3], [1.5, 2], [3, 5]]#[[3, 5]]
#bias_param_list=[[3, 5]]
failf = open('data2/fail_list.txt', 'w')
success_f =  open('data2/success_list.txt', 'w')
for fname in fname_list:
	# if os.path.exists(get_HTML_fname(fname)):
	#  	print 'continue %s' % get_HTML_fname(fname)
	#  	continue
	with simplePDF2HTML(fname, get_HTML_fname(fname)) as test:
		print "trying to convert file {0}".format(test.pdf_path)

		succeed = False
		if COUNT:
			cnt_total += 1
			for bias_param in bias_param_list:
				#try:
				print "processing {0}st file".format(cnt_total)
				# print "trying parameter set {1}:{0}".format(bias_param,cnt_total)
				test.convert(bias_param)
				cnt_success += 1
				print "succeed"
				succeed = True
				break
				#except Exception, e:
				#	print "didn't succeed"
			if not succeed:
				print "failed to convert file {0}".format(test.pdf_path)
				unsuccess.append(copy.copy(test.pdf_path))
				print >>failf, test.pdf_path
			else:
				print >>success_f,  test.pdf_path
		else:
			for bias_param in bias_param_list:
				print "trying parameter set {0}".format(bias_param)
				test.convert(bias_param)
if COUNT:
	print "successfully converted {0} files out of {1} files".format(cnt_success, cnt_total)
	if cnt_total > cnt_success:
		print "problematic files include: "
		for unsuccess_name in unsuccess:
			print "    {0}".format(unsuccess_name)
