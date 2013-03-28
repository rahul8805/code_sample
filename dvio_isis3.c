#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <regex.h>
#include "parser.h"
#include "endian_norm.h"
#include <errno.h>
#include "header.h"

#define ISIS_DEBUG 1
#define debug(x)	fprintf(stderr, x)

/* 2 formats for isis data */
#define TILE		0
#define MY_BSQ		1

/* msb or lsb */
#define MY_LSB 0
#define MY_MSB 1


/************************************/
#define MAXOBJ 10

#define FIELD_GEN_OBJ_CLASS "GenObjClass"
#define FIELD_OBJ_CLASS     "Object"

#define GEN_OBJ_CLASS_HISTOGRAM "histogram"
#define GEN_OBJ_CLASS_HISTORY   "history"
#define GEN_OBJ_CLASS_IMAGE     "image"
#define GEN_OBJ_CLASS_QUBE      "qube"
#define GEN_OBJ_CLASS_TABLE     "table"
#define GEN_OBJ_CLASS_GROUP     "group"
#define GEN_OBJ_CLASS_PTR       "ptr"

#define KW_GROUP "GROUP"
#define KW_END_GROUP "END_GROUP"

/* NOTE: Only add bonafide PDS objects */
static const char *handledObjTypes[] = { 
	GEN_OBJ_CLASS_HISTOGRAM,
	GEN_OBJ_CLASS_HISTORY,
	GEN_OBJ_CLASS_IMAGE,
	GEN_OBJ_CLASS_QUBE,
	GEN_OBJ_CLASS_TABLE
	/* NOTE: Neither groups nor ptrs are not PDS objects, that's why they are not listed here */
};
static const int nHandledObjTypes = sizeof(handledObjTypes)/sizeof(char *);

static int genObjClassCmpr(const void *v1, const void *v2){
	const char *s1 = *(const char **)v1;
	const char *s2 = *(const char **)v2;

	if (s1 == NULL && s2 == NULL)
		return 0;
	if (s1 == NULL && s2 != NULL)
		return -1;
	if (s1 != NULL && s2 == NULL)
		return 1;
	return strcasecmp(s1,s2);
}

// Temp structures... Will be used for name mangling...
struct dict_entry
{
	char name[20];
	int count;
	int type;
	struct dict_entry *next;
};

struct table_info
{
	int startbyte;
	int bytes;
	int records;
	char *data_type;
	char *byte_ordering;
	int bytes_per_row;
};

struct table_dictionary
{
	char * tbl_name;
	char * loc_name;
};
struct table_dictionary tbl_dict[100];
int tbl_cnt=0;

void reverse_bytes(char *p, char *q);
void reverse_byte_order(void *vptr, int size, int n);
int get_size_of_data_type(struct table_info tf);
void extract_table_data_and_add(char *filename, Var *ob, struct table_info tf);
char * get_data_type_str_table(Var *tbl_ob);
void process_data_for_all_tables(char *filename, Var **table, int cnt);

/* The following function performs the actual task of renaming the fields
 * based on the type of reform needed... The string to be renamed first needs
 * to be designated as either as an object name or a group name as this
 * procedure takes into account this fact while renaming...
 */
void reform_names(OBJDESC *ob, char *nm, int cnt, int reform_type)
{
	OBJDESC *p;
	KEYWORD *kw;
	char buf[10];
	int c = 1;

	// Based on the reform type, we can figure out whether object or group names should be renamed...
	for(p=ob->first_child ;p!=NULL;p=p->right_sibling)
		if(strcasecmp(p->obj_class, nm)==0 && reform_type==0)
		{
			// Means object needs to be renamed...
			int_to_ascii(c,buf);
			strcat(p->obj_class, buf);
			c++;
		}
		else
		{
			// Reset counter...
			c = 1;

			// Means groups need to be renamed...
			// Just to be extra sure, we check for the "name" field and proceed only if it says "group"...
			for(kw=p->first_keyword;kw!=NULL;kw=kw->right_sibling)
				if(strcasecmp(kw->name,"group")==0 && strcasecmp(kw->value,nm)==0)
				{
					int_to_ascii(c,buf);
					strcat(kw->value, "_");
					strcat(kw->value, buf);
					c++;
					//replace_field_name(kw);
					//strcpy(kw->name,kw->right_sibling->value);
					//strcpy(kw->value,kw->name);
				}
		}
}

// The following function returns a pointer to an element that is being searched in the list.
// It returns a NULL pointer if the element is not found...
struct dict_entry * find(char *find_name, struct dict_entry *de)
{
	struct dict_entry *p=de;

	while(p!=NULL)
		if(strcasecmp(p->name,find_name)==0)
			return p;
		else
			p=p->next;

	return NULL;
}

// Creates a new node, and populates the fields based on the arguments passed.
// The pointer to the beginning of the linked list is accordingly manipulated... (similar to building a stack)
// This list keeps track of the objects and group names that are duplicates...
void make_new_node(struct dict_node **root, char *new_name, int type)
{
	struct dict_entry *p = (struct dict_entry *)malloc(sizeof(struct dict_entry));

	// Once the node is created, it is populated based on the information that is passed...
	strcpy(p->name, new_name);
	p->count=1;

	// The type tells what kind of "string" is being tracked... 0 means object name and 1 means group name...
	p->type = type;
	p->next = *root;
	*root = p;
}

// The following function just claims the memory that is being used by the linked list...
void re_claim_memory(struct dict_entry *root)
{
	struct dict_entry *p, *q;

	p=q=NULL;

	p=root;
	while(p!=NULL)
	{
		q=p;
		p=p->next;
		free(q);
	}
}

/* The following function leads the renaming process.
 * Makes several synchronized calls to other procedures.
 * Manipulates the OBJDESC linked list that was created
 * by parsing the file...
 */
int mangle_duplicate_names(OBJDESC *ob)
{
	struct dict_entry *root, *q;
	OBJDESC *p;
	KEYWORD *kw;
	int cnt = 0;

	root=NULL;

	// First we find the duplicate names that may be present in the doubly linked list...
	for(p=ob->first_child ;p!=NULL;p=p->right_sibling)
	{
		if((q=find(p->obj_class, root))!=NULL)
			q->count++;
		else
			make_new_node(&root, p->obj_class, 0);

		// Next, check for group names that may be duplicate
		for(kw=p->first_keyword;kw!=NULL;kw=kw->right_sibling)
			if(strcasecmp(kw->name,"group")==0 && (q=find(kw->value, root))!=NULL)
				q->count++;
			else if(strcasecmp(kw->name,"group")==0)
				make_new_node(&root, kw->value, 1);
	}
	// When execution reaches this point, we will have a list of names that may or may not contain duplicates...

	// Next, we traverse the list of duplicates and perform the name mangling...
	for(q=root;q!=NULL;q=q->next)
		if(q->count>1)
		{
			fprintf(stderr, "\"%s\" requires renaming: ", q->name);
			reform_names(ob, q->name, q->count, q->type);
			fprintf(stderr, "Done... (Duplicacy count: %d)\n", q->count);

			if(strcasecmp(q->name, "table")==0)
				cnt = q->count;
		}

	// Free all root elements...
	re_claim_memory(root);

	return cnt;
}

// The following function replaces the strings "table" and "field" with theis corresponding names so that they can be accessed
void rename_tables_and_fields(OBJDESC *ob)
{
	struct dict_entry *root, *q;
	OBJDESC *p;
	KEYWORD *kw;
	int cnt = 0;

	root=NULL;

	// First we find the duplicate names that may be present in the doubly linked list...
	for(p=ob->first_child ;p!=NULL;p=p->right_sibling)
	{
		if(strncasecmp(p->obj_class, "table", 5)==0)
		{
			// If the identified keyword is "table", change the name...
			p->obj_class = p->first_keyword->value;

			// Next, check for group names that may be duplicate
			for(kw=p->first_keyword;kw!=NULL;kw=kw->right_sibling)
				if(strncasecmp(kw->name, "group", 5)==0)
					kw->value=kw->right_sibling->value;
		}
	}
}


// The following function reverses a string...
void reverse_string(char *str)
{
	char *p,*q,tmp;

	p=str;
	q=str+strlen(str)-1;

	while(p<q)
	{
		tmp=*p;
		*p=*q;
		*q=tmp;

		p++;
		q--;
	}
}

// The following function converts an integer value to its string equivalent...
void int_to_ascii(int num, char *buf)
{
	int n=num;
	int r=0;
	int i=0;

	while (n!=0)
	{
		r=n%10;
		buf[i++]=r+'0';
		n=n/10;
	}

	buf[i]='\0';
	reverse_string(buf);
}

// The following method will reverse the bytes by swapping...
void reverse_bytes(char *p, char *q)
{
	char c;
	while (p<q)
	{
		c=*p;
		*p=*q;
		*q=c;

		p++;
		q--;
	}
}

// The following method will reverse the bytes in the array based on the data type...
void reverse_byte_order(void *vptr, int size, int n)
{
	// Since we're gonna do this byte by byte, use a char ptr...
	char *p,*q;
	int i;

	p=vptr; // byte 0
	q=vptr + size - 1; // byte 7

	for(i=0;i<n;i++)
	{
		reverse_bytes(p,q); // reverses bytes 0 through 7...
		p=q+1; // byte 8
		q=q+size; // byte 15
	}
}

// The following method will return the size of the data type...
int get_size_of_data_type(struct table_info tf)
{
	if(strcasecmp(tf.data_type, "int")==0)
		return sizeof(int);
	if(strcasecmp(tf.data_type, "char")==0)
		return sizeof(char);
	if(strcasecmp(tf.data_type, "double")==0)
		return sizeof(double);

	return sizeof(double);
}

// The following function returns the size of the "field" in bytes...
int get_field_size(Var *ob)
{
	Var** substructs = NULL;
	char** keys = NULL;
	int count = 0;
	int i;

	if(!get_substructs(ob, &substructs, &keys, &count))
		return NULL;

	for(i=0;i<count;i++)
		if(strcasecmp(keys[i],"size")==0)
			return V_INT(substructs[i]);

	return 0;
}

// Creates the "data" object for every field...
Var * create_field_data(Var *ob, void *vptr, struct table_info tf, int field_no)
{
	Var *data=new_struct(0);

	int data_type_size = get_size_of_data_type(tf);
	int field_size = get_field_size(ob); // Not to be confused with data type size...
	int row_size = tf.bytes_per_row;

	// Allocate memory...
	void *field_data = malloc(data_type_size * field_size);
	void *temp = field_data;

	int i, byte_offset;

	i=byte_offset=0;

	// Set the vptr to the appropriate byte...
	vptr = vptr + (field_no * data_type_size);

	for(i=0;i<field_size;i++)
	{
		memcpy(temp, vptr, data_type_size);

		// For example, for row size of 64 bytes and field number 1, the bytes that need to be copied will be 8-15 and 72-79...
		vptr = vptr + row_size;

		// Advance the temp ptr as well...
		temp = temp + data_type_size;
	}

	// Return a new Var object with the data...
	if(strcasecmp(tf.data_type, "byte") == 0)
		return newVal(BSQ, tf.records, field_size, 1, BYTE, vptr);
	if(strcasecmp(tf.data_type, "short") == 0)
		return newVal(BSQ, tf.records, field_size, 1, SHORT, vptr);
	if(strcasecmp(tf.data_type, "int") == 0)
		return newVal(BSQ, tf.records, field_size, 1, INT, vptr);
	if(strcasecmp(tf.data_type, "float") == 0)
		return newVal(BSQ, tf.records, field_size, 1, FLOAT, vptr);
	if(strcasecmp(tf.data_type, "vax_float") == 0)
		return newVal(BSQ, tf.records, field_size, 1, VAX_FLOAT, vptr);
	if(strcasecmp(tf.data_type, "vax_integer") == 0)
		return newVal(BSQ, tf.records, field_size, 1, VAX_INTEGER, vptr);
	if(strcasecmp(tf.data_type, "int64") == 0)
		return newVal(BSQ, tf.records, field_size, 1, INT64, vptr);
	if(strcasecmp(tf.data_type, "double") == 0)
		return newVal(BSQ, tf.records, field_size, 1, DOUBLE, vptr);

	// Return double data by default...
	return newVal(BSQ, tf.records, field_size, 1, DOUBLE, vptr);

}

// The following function just adds the "data" chunk as a whole to the table...
void add_entire_chunk(Var *ob, void *vptr, struct table_info tf)
{
	int rows;
	int fields;
	int data_type_size;
	void *ptr;
	Var *v;

	data_type_size = get_size_of_data_type(tf);
	rows = tf.records;
	fields = tf.bytes/rows/data_type_size;

	// Return a new Var object with the data...
	if(strcasecmp(tf.data_type, "byte") == 0)
		v = newVal(BSQ, tf.records, fields, 1, BYTE, vptr);
	if(strcasecmp(tf.data_type, "short") == 0)
		v = newVal(BSQ, tf.records, fields, 1, SHORT, vptr);
	if(strcasecmp(tf.data_type, "int") == 0)
		v = newVal(BSQ, tf.records, fields, 1, INT, vptr);
	if(strcasecmp(tf.data_type, "float") == 0)
		v = newVal(BSQ, tf.records, fields, 1, FLOAT, vptr);
	if(strcasecmp(tf.data_type, "vax_float") == 0)
		v = newVal(BSQ, tf.records, fields, 1, VAX_FLOAT, vptr);
	if(strcasecmp(tf.data_type, "vax_integer") == 0)
		v = newVal(BSQ, tf.records, fields, 1, VAX_INTEGER, vptr);
	if(strcasecmp(tf.data_type, "int64") == 0)
		v = newVal(BSQ, tf.records, fields, 1, INT64, vptr);
	if(strcasecmp(tf.data_type, "double") == 0)
		v = newVal(BSQ, tf.records, fields, 1, DOUBLE, vptr);

	add_struct(ob, "data", v);
}

// The following method returns the locator string...
char * get_locator(char *tbl_name)
{
	return tbl_dict[tbl_name[5]-49].loc_name;
}


// The following function extracts the data from the file by seeking to a particular offset...
void extract_table_data_and_add(char *filename, Var *ob, struct table_info tf)
{
	FILE *fp;
	void *vptr;
	int start, end;
	int n_bytes;
	int no_of_elements;
	int no_of_elements_in_a_row;
	int n_recs;
	int bytes_per_row;
	int data_type_size = 0;

	// Set boundaries for the file data to be read...
	fp=fopen(filename, "rb");
	start = tf.startbyte;
	n_bytes = tf.bytes;
	end = start + n_bytes;
	n_recs = tf.records;
	bytes_per_row = tf.bytes_per_row;

	// Determine the size of the data type...
	data_type_size = get_size_of_data_type(tf);

	// Chunk to read the data into...
	vptr = (void *)malloc(n_bytes + 10);

	// Go to the start byte
	fseek(fp, start-1, SEEK_SET);

	// Read the information present at that offset...
	fread(vptr, 1, n_bytes, fp);

	// Establish the number of elements by dividing the total_no_of_bytes/sizeof(single_element)
	no_of_elements_in_a_row = bytes_per_row/data_type_size;
	no_of_elements = no_of_elements_in_a_row * n_recs;

	// If the byte ordering is LSB (meaning little endian), the byte ordering needs to be reversed...
	if(strcasecmp(tf.byte_ordering,"lsb")==0 && data_type_size > 1)
		reverse_byte_order(vptr, data_type_size, no_of_elements);

	// Add the data to individual fields...
	add_data_to_table_fields(ob, vptr, tf);
}

// The following method determines the type of data that is being extracted...
char * get_data_type_str_table(Var *tbl_ob)
{
	Var** substructs = NULL;
	char** keys = NULL;
	int count = 0;
	int i;
	char temp[20];

	// Unwrap the field object and check out what kind of data type is specified...
	if(!get_substructs(tbl_ob, &substructs, &keys, &count))
		return NULL;

	for(i=0;i<count;i++)
		if(strcasecmp(keys[i],"type")==0)
			return V_STRING(substructs[i]);

	// Else, return double by default...
	strcpy(temp, "double");
	return strdup(temp);
}

// Processes and adds data to all the tables...
void process_data_for_all_tables(char *filename, Var **table, int cnt)
{
	int i = 0, j = 0;
	Var** substructs = NULL;
	char** keys = NULL;
	int count;
	struct table_info tf;

	for(i=0;i<cnt;i++)
	{
		if(!get_substructs(table[i], &substructs, &keys, &count))
			return NULL;

		// Find out the startbyte, no of bytes, recs and the byte ordering...
		for(j=0;j<count;j++)
		{
			if(strcasecmp(keys[j], "startbyte")==0)
				tf.startbyte=V_INT(substructs[j]);
			if(strcasecmp(keys[j], "bytes")==0)
				tf.bytes=V_INT(substructs[j]);
			if(strcasecmp(keys[j], "records")==0)
				tf.records=V_INT(substructs[j]);
			if(strcasecmp(keys[j], "byteorder")==0)
				tf.byte_ordering = V_STRING(substructs[j]);
			if(strcasecmp(keys[j], tbl_dict[i].loc_name)==0)
				tf.data_type = get_data_type_str_table(substructs[j]);
		}

		// Determine the number of bytes per row...
		tf.bytes_per_row = tf.bytes/tf.records;

		// When the execution reaches this point, we will have the information needed to extract the data...
		// Next, we need to determine if the data is ascii or non-ascii...
		if(strcasecmp(tf.data_type, "ascii")==0)
		{
			// Process the data as ascii...
			process_data(filename, table[i], "Table");
		}
		else
			extract_table_data_and_add(filename, table[i], tf);
	}
}

// Check if the incoming object is a table...
int is_table(Var *obj)
{
	Var** substructs = NULL;
	Var *tmp;
	char *tk;
	char** keys = NULL;
	int count;

	// Unwrap the structure
	if( !get_substructs(obj, &substructs, &keys, &count) )
			return 0;

	tmp = *substructs;
	tk = *keys;

	// Return true only if GenObjClass contains the table keyword...
	return strncasecmp((*substructs)->value.string, "table", 5)==0?1:0;
}

int is_file_isis3(char **keys, int count)
{
	int i;
	int confidence_level=0;

	// If there are too many objects (say more than 20), there is a possibility that the file may not be in a proper format...
	if(count >=20)
		confidence_level--;

	for(i = 0; i < count; i++)
	{
		if(strcasecmp(keys[i], "isiscube")==0)
			confidence_level++;
		if(strcasecmp(keys[i], "history")==0)
			confidence_level++;
		if(strcasecmp(keys[i], "label")==0)
			confidence_level++;
	}

	// If the confidence level is greater than or equal to 2, we could be almost sure (if not a 100%) that the file is ISIS3 complaint...
	return confidence_level>=2?1:0;
}

// Processes the file offsets so that data can be added from that offset...
void process_data(char *filename, Var *ob, char *obj_name)
{
	dataKey dk;
	int startbyte;
	int bytes;
	Var** substructs = NULL;
	char** keys = NULL;
	int count, i;

	char tmp[10];
	Var* t;

	strcpy(tmp, obj_name);

	dk.FileName = filename;
	dk.Name = tmp;

	// Unwrap the contents of the history object...
	if( !get_substructs(ob, &substructs, &keys, &count) )
		return;

	// Loop through the keys and try to find out the startbyte and the number of bytes to be read...
	for(i=0;i<count;i++)
	{
		strcpy(tmp,keys[i]);
		t=substructs[i];

		// Since the offsets in ISIS3 are zero-based, we need to decrement one byte...
		if(strcasecmp(keys[i], "startbyte")==0)
		{
			dk.dptr = V_INT(substructs[i]);
			dk.dptr--;
		}
		else if(strcasecmp(keys[i], "bytes")==0)
			dk.size = V_INT(substructs[i]);
	}

	add_ascii_data(&dk, ob);
}