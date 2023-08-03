// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use lazy_static::lazy_static;
use rdkafka::{
    producer::{BaseProducer, BaseRecord},
    ClientConfig,
};
use std::{thread, time::Duration};

pub struct KafkaProducer {
    producer: BaseProducer,
}

impl KafkaProducer {
    pub fn new() -> Self {
        let producer: BaseProducer =
            ClientConfig::new().set("bootstrap.servers", "localhost:9092").create().expect("Producer creation error");

        KafkaProducer { producer }
    }

    pub fn emit_event(&self, event_data: &str, topic: &str) {
        for i in 1..100 {
            println!("sending message");

            self.producer
                .send(BaseRecord::to(topic).key(&format!("key-{}", event_data)).payload(&format!("value-{}", i)))
                .expect("failed to send message");

            thread::sleep(Duration::from_secs(3));
        }
    }
}

lazy_static! {
    pub static ref KAFKA_PRODUCER: KafkaProducer = KafkaProducer::new();
}
