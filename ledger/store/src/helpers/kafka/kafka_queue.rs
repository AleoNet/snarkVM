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

use crate::helpers::kafka::KAFKA_PRODUCER;
pub struct KafkaQueue {
    pub messages: Vec<(Vec<u8>, Vec<u8>)>,
}

impl KafkaQueue {

    pub fn new() -> Self {
        KafkaQueue {
            messages: Vec::new(),
        }
    }

    pub fn put(&mut self, key: Vec<u8>, value: Vec<u8>) {
        self.messages.push((key, value));
    }

    pub fn send_messages(&self, topic: &str) {
        for (key, value) in &self.messages {
            KAFKA_PRODUCER.emit_event(&String::from_utf8_lossy(&value), topic);
        }
    }

    #[cfg(test)]
    pub fn get_messages(&self) -> &Vec<(Vec<u8>, Vec<u8>)> {
        &self.messages
    }
}