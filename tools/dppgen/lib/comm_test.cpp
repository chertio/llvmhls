#include "comm.h"

#define NUM_TOKEN 17
#define NUM_CONSUMER 3
template<typename T>
struct channel_info_4_consumer
{
	struct fifo_channel<T>* channel_ptr;
	int assigned_slot;
	void init(fifo_channel<T>* _channel_ptr, int _assigned_slot)
	{
		channel_ptr = _channel_ptr;
		assigned_slot = _assigned_slot;
	}
};

typedef struct channel_info_4_consumer<int> consumer_t_info;	

// only for test reasons
// actual push function would be templated
void* push(void* l)
{
	struct fifo_channel<int>* to_fifo = (struct fifo_channel<int>*)l;
	for(int i=0; i<NUM_TOKEN; i++)
	{
		printf("write %d\n", i);
		to_fifo->write(i);		
	}
}


void* pop(void* l)
{
	consumer_t_info* my_t_info = (consumer_t_info*)l;
	struct fifo_channel<int>* from_fifo = my_t_info->channel_ptr;
	int my_assigned_slot = my_t_info->assigned_slot;
	for(int i=0; i<NUM_TOKEN; i++)
	{
		int result = from_fifo->read(my_assigned_slot);
		printf("read %d from %d\n",result, my_assigned_slot);
	}
}

int main(int argc, char* argv[])
{

	pthread_t threads[1+NUM_CONSUMER];
	pthread_attr_t attr;
  
	struct fifo_channel<int>* my_fifo=new struct fifo_channel<int>;
		
  	my_fifo->init(NUM_CONSUMER);
	
	pthread_attr_init(&attr);
	pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
  	
	pthread_create(&threads[0], &attr, push, my_fifo);
	int consumer_ind;
	for(consumer_ind = 0; consumer_ind < NUM_CONSUMER; consumer_ind++)
	{	
		consumer_t_info* cur_consumer_t_info = new consumer_t_info;
		cur_consumer_t_info->init(my_fifo, consumer_ind);
		
  		pthread_create(&threads[1+consumer_ind], &attr, pop, cur_consumer_t_info);
  	}
	int i;
  	for (i=0; i<NUM_CONSUMER+1; i++) {
    	pthread_join(threads[i], NULL);
  	}
  	printf ("Main(): Waited on %d  threads. Done.\n", NUM_CONSUMER+1);

  /* Clean up and exit */
  pthread_attr_destroy(&attr);
  //pthread_mutex_destroy(&channel_mutex);
  //pthread_cond_destroy(&channel_cond);
  pthread_exit(NULL);

}








